-- Prove2me | solution 1 for ValiantBorder.borderDetToCircuit
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:29:52.244964+00:00
-- url     : https://prove2.me/submissions/17565d63-7baf-481c-bfdf-ed749ca08ea4

/- Coefficient specialization and removal of padding for the Prove2Me border determinant model.
The geometric dependency uses Guo, Saxena and Sinhababu, CCC 2018, Theorem 15.
The Laurent-polynomial coefficient embedding is adapted from Claude (Anthropic),
VP ≠ VNP over every field, Nc/Rate/Truncate.lean, Apache-2.0.
Copyright (c) 2026 Anthropic, PBC (adapted material). -/
import Theorems.Thm_ValiantBorder_polynomialImageArc
import Theorems.Thm_ValiantBorder_affineDetCircuit
import Theorems.Thm_ValiantBorder_laurentTransfer
import Definitions.Def_GCT_determinantal_complexity

open MvPolynomial
open Filter Topology
namespace BorderDet

/- Affine curve selection for the image of a finite complex polynomial map.
This is the Laurent-series consequence of Guo, Saxena and Sinhababu, Theorem 15. -/
def PolynomialCurveSelection : Prop :=
  ∀ (I J : Type) [Fintype I] [Fintype J] (F : J → MvPolynomial I ℂ) (p : J → ℂ),
    (∀ g : MvPolynomial J ℂ, aeval F g = 0 → eval p g = 0) →
    ∃ (K : Type) (_ : Field K) (j : ℂ →+* K)
      (x : I → LaurentSeries K) (q : J → PowerSeries K),
      ∀ i, eval₂Hom ((algebraMap K (LaurentSeries K)).comp j) x (F i) = HahnSeries.ofPowerSeries ℤ K (q i) ∧
        PowerSeries.constantCoeff (q i) = j (p i)

theorem relations_of_convergent {I J : Type} {F : J → MvPolynomial I ℂ} {p : J → ℂ}
    {v : ℕ → I → ℂ} (h : ∀ j, Tendsto (fun k => eval (v k) (F j)) atTop (𝓝 (p j))) :
    ∀ g : MvPolynomial J ℂ, aeval F g = 0 → eval p g = 0 := by
  intro g hg
  have ht := (MvPolynomial.continuous_eval g).continuousAt.tendsto.comp (tendsto_pi_nhds.2 h)
  have hz (k : ℕ) : eval (fun j => eval (v k) (F j)) g = 0 := by
    change aeval (fun j => aeval (v k) (F j)) g = 0
    rw [← comp_aeval_apply, hg, map_zero]
  exact tendsto_nhds_unique ht (by simpa only [Function.comp_def,hz] using (tendsto_const_nhds (x:= (0:ℂ)) (f:=atTop)))

noncomputable def lin {V R : Type} [Fintype V] [CommRing R] (a : V → R) : MvPolynomial V R :=
  ∑ v, C (a v) * X v

theorem linear_coefficients {V : Type} [Fintype V] {p : MvPolynomial V ℂ} (h : p.IsHomogeneous 1) :
    ∃ a : V → ℂ, lin a = p := by
  have hs : p ∈ homogeneousSubmodule V ℂ 1 := h
  rw [homogeneousSubmodule_one_eq_span_X] at hs
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hs
  exact ⟨a, by simpa only [lin,smul_eq_C_mul] using ha⟩

abbrev Param (n : ℕ) (V : Type) := Fin n × Fin n × V

noncomputable def pencil {V R : Type} [Fintype V] [CommRing R] {n : ℕ} (v : Param n V → R) :
    Matrix (Fin n) (Fin n) (MvPolynomial V R) := Matrix.of fun i j => lin (fun t => v (i,j,t))

noncomputable def universalDet (n : ℕ) (V : Type) [Fintype V] :
    MvPolynomial V (MvPolynomial (Param n V) ℂ) := (pencil X).det

theorem specialize {V R : Type} [Fintype V] [CommRing R] {n : ℕ}
    (h : ℂ →+* R) (v : Param n V → R) :
    map (eval₂Hom h v) (universalDet n V) = (pencil v).det := by
  rw [universalDet, RingHom.map_det]
  congr 1
  ext i j : 1
  simp [Matrix.map_apply,pencil,lin,eval₂Hom_X']

noncomputable def assemble {V R : Type} [CommRing R] (D : Finset (V →₀ ℕ)) (q : D → R) :
    MvPolynomial V R := ∑ t, monomial t.val (q t)

theorem coeff_assemble {V R : Type} [CommRing R] {D : Finset (V →₀ ℕ)} (q : D → R) (d : V →₀ ℕ) [DecidableEq V] :
    coeff d (assemble D q) = if h : d ∈ D then q ⟨d,h⟩ else 0 := by
  classical
  rw [assemble,coeff_sum]
  by_cases h : d ∈ D
  · rw [dif_pos h, Finset.sum_eq_single (⟨d,h⟩ : D)]
    · simp
    · intro b _ hne
      rw [coeff_monomial, if_neg (fun he => hne (Subtype.ext he))]
    · simp
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro b _
    have ne : (b : V →₀ ℕ) ≠ d := fun he => h (he ▸ b.property)
    rw [coeff_monomial, if_neg ne]

theorem det_arc_of_selection (hc : PolynomialCurveSelection) {n : ℕ} {V : Type} [Fintype V]
    {p : MvPolynomial V ℂ} (h : GCT.HasBorderLinearDetRep n p) :
    ∃ (K : Type) (_ : Field K) (j : ℂ →+* K) (v : Param n V → LaurentSeries K) (Q : MvPolynomial V (PowerSeries K)),
      map (HahnSeries.ofPowerSeries ℤ K) Q = (pencil v).det ∧ map PowerSeries.constantCoeff Q = map j p := by
  classical
  obtain ⟨A,hA,hlim⟩ := h
  choose c hcA using fun k i j => linear_coefficients (hA k i j)
  let v (k : ℕ) : Param n V → ℂ := fun t => c k t.1 t.2.1 t.2.2
  have hv k : pencil (v k) = A k := Matrix.ext (fun i j => hcA k i j)
  let U := universalDet n V
  let D := U.support ∪ p.support
  let F (d : D) := coeff d.val U
  have hcoeff k (d : V →₀ ℕ) : eval (v k) (coeff d U) = coeff d ((A k).det) := by
    rw [← hv, ← specialize (RingHom.id ℂ), coeff_map]
    rfl
  have ht (d : D) : Tendsto (fun k => eval (v k) (F d)) atTop (𝓝 (coeff d.val p)) := by
    simpa only [F,hcoeff] using hlim d.val
  obtain ⟨K,_,j,a,q,ha⟩ := hc (Param n V) D F (fun d => coeff d.val p) (relations_of_convergent ht)
  refine ⟨K,_,j,a,assemble D q,?_,?_⟩
  · rw [← specialize ((algebraMap K (LaurentSeries K)).comp j)]
    apply MvPolynomial.ext
    intro d
    rw [coeff_map,coeff_map,coeff_assemble]
    by_cases hd : d ∈ D
    · rw [dif_pos hd]; exact (ha ⟨d,hd⟩).1.symm
    · have hz : coeff d U = 0 := notMem_support_iff.mp (fun h => hd (Finset.mem_union_left _ h))
      simp [hd, ← show U = universalDet n V from rfl,hz]
  · ext d
    rw [coeff_map,coeff_map,coeff_assemble]
    by_cases hd : d ∈ D
    · rw [dif_pos hd]; exact (ha ⟨d,hd⟩).2
    · rw [dif_neg hd,map_zero]
      have hz : coeff d p = 0 := notMem_support_iff.mp (fun h => hd (Finset.mem_union_right _ h))
      rw [hz, map_zero]
end BorderDet

open MvPolynomial
namespace BorderDet
variable {R S V : Type} [CommRing R] [CommRing S]

noncomputable def dehomogenize : MvPolynomial (Option V) R →ₐ[R] MvPolynomial V R :=
  bind₁ (fun v => v.elim 1 X)

theorem map_dehomogenize (h : R →+* S) (Q : MvPolynomial (Option V) R) :
    map h (dehomogenize Q) = dehomogenize (map h Q) := by
  rw [dehomogenize, map_bind₁]
  congr 2
  funext v
  cases v <;> simp

theorem dehomogenize_perm (m n : ℕ) :
    dehomogenize (GCT.paddedPerm m n) = Statement.perm ℂ m := by
  simp [GCT.paddedPerm, GCT.permPolyPad, Matrix.permanent, Statement.perm, dehomogenize,
    bind₁_X_right, Matrix.of_apply]

theorem computes_dehomogenize {q : MvPolynomial (Option V) R} {s : ℕ} (h : Statement.Computes q s) :
    Statement.Computes (dehomogenize q) s := by
  obtain ⟨l,hl,k,hk,rfl⟩ := h
  refine ⟨fun j => dehomogenize (l j),?_,k,hk,rfl⟩
  intro j hj
  rcases hl j hj with ⟨v,rflv⟩ | ⟨a,ha⟩ | ⟨i,hi,t,ht,e⟩ | ⟨i,hi,t,ht,e⟩
  · cases v with
    | none => exact Or.inr (Or.inl ⟨1, by simp [rflv,dehomogenize,bind₁_X_right]⟩)
    | some v => exact Or.inl ⟨v, by simp [rflv,dehomogenize,bind₁_X_right]⟩
  · exact Or.inr (Or.inl ⟨a, by simp [ha,dehomogenize,bind₁_C_right]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i,hi,t,ht,by simp [e]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i,hi,t,ht,by simp [e]⟩))

theorem of_regular_output {F V : Type} [Field F] (Q : MvPolynomial V (PowerSeries F))
    {s : ℕ} (hc : Statement.Computes (map (HahnSeries.ofPowerSeries ℤ F) Q) s) :
    Statement.Approximates (map (PowerSeries.constantCoeff) Q) s := by
  refine ⟨_,hc,fun d i hi => ?_⟩
  rw [coeff_map,coeff_map]
  rcases eq_or_lt_of_le hi with rfl | hneg
  · simp only [if_pos rfl]
    change (↑(coeff d Q) : LaurentSeries F).coeff (0 : ℤ) = _
    rw [PowerSeries.coeff_coe]
    simp
  · rw [if_neg hneg.ne]
    change (↑(coeff d Q) : LaurentSeries F).coeff i = 0
    rw [PowerSeries.coeff_coe,if_pos hneg]


end BorderDet

namespace BorderLaurent
open MvPolynomial
def IsStep {R X : Type*} [CommSemiring R] (l : ℕ → MvPolynomial X R) (k : ℕ) : Prop :=
  (∃ v : X, l k = MvPolynomial.X v) ∨ (∃ a : R, l k = C a) ∨
    (∃ i < k, ∃ j < k, l k = l i + l j) ∨ (∃ i < k, ∃ j < k, l k = l i * l j)

def Computes {R X : Type*} [CommSemiring R] (f : MvPolynomial X R) (s : ℕ) : Prop :=
  ∃ l : ℕ → MvPolynomial X R, (∀ k < s, IsStep l k) ∧ ∃ k < s, l k = f

theorem Computes.map {R S X : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) {f : MvPolynomial X R} {s : ℕ} (h : Computes f s) :
    Computes (MvPolynomial.map φ f) s := by
  obtain ⟨l, hl, k, hk, rfl⟩ := h
  refine ⟨fun i => MvPolynomial.map φ (l i), ?_, k, hk, rfl⟩
  intro j hj
  rcases hl j hj with ⟨v, hv⟩ | ⟨a, ha⟩ | ⟨i, hi, t, ht, he⟩ | ⟨i, hi, t, ht, he⟩
  · exact Or.inl ⟨v, by simp [hv]⟩
  · exact Or.inr (Or.inl ⟨φ a, by simp [ha]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, hi, t, ht, by simp [he]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨i, hi, t, ht, by simp [he]⟩))


variable {F : Type*} [CommRing F]

noncomputable def laurentToSeries (F : Type*) [CommRing F] : LaurentPolynomial F →+* LaurentSeries F :=
  AddMonoidAlgebra.liftNCRingHom HahnSeries.C
    { toFun := fun n => HahnSeries.single n.toAdd 1
      map_one' := rfl
      map_mul' := fun a b => by rw [HahnSeries.single_mul_single, toAdd_mul, one_mul] }
    fun _ _ => Commute.all _ _

/-- The series of a Laurent polynomial has the same coefficients. -/
@[simp] theorem coeff_laurentToSeries (x : LaurentPolynomial F) (i : ℤ) :
    (laurentToSeries F x).coeff i = x.coeff i := by
  induction x using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, HahnSeries.coeff_add, hp, hq, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  | C_mul_T n a =>
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    classical
    rw [laurentToSeries, AddMonoidAlgebra.liftNCRingHom_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]
    change a * (HahnSeries.single n (1 : F)).coeff i = _
    rw [HahnSeries.coeff_single]
    by_cases h : i = n
    · simp [h]
    · simp [h, Ne.symm h]


end BorderLaurent

namespace BorderDet
open MvPolynomial
theorem computes_widen {V R : Type} [CommRing R] {f : MvPolynomial V R} {s t : ℕ}
    (h : Statement.Computes f s) (hst : s ≤ t) : Statement.Computes f t := by
  rcases h with ⟨g,hg,k,hk,hf⟩
  let l i := if i < s then g i else C 0
  have eq (i : ℕ) (hi : i < s) : l i = g i := if_pos hi
  refine ⟨l, ?_, k, lt_of_lt_of_le hk hst, (eq _ hk).trans hf⟩
  intro i hi
  by_cases h : i < s
  · rw [eq _ h]
    rcases hg i h with hv | hv | ⟨a,ha,b,hb,hh⟩ | ⟨a,ha,b,hb,hh⟩
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
    · exact Or.inr (Or.inr (Or.inl ⟨a,ha,b,hb,by rw [eq _ (ha.trans h), eq _ (hb.trans h)]; exact hh⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨a,ha,b,hb,by rw [eq _ (ha.trans h), eq _ (hb.trans h)]; exact hh⟩))
  · exact Or.inr (Or.inl ⟨0,if_neg h⟩)
end BorderDet

open MvPolynomial BorderDet
theorem solution :
    ∃ a : ℕ, ∀ m n : ℕ, m ≤ n →
      GCT.HasBorderLinearDetRep n (GCT.paddedPerm m n) →
      Statement.Approximates (Statement.perm ℂ m) ((m + n + 2) ^ a) := by
  classical
  refine ⟨16,fun m n _ h => ?_⟩
  obtain ⟨K, _, j, v, Q, hdet, hQ⟩ := det_arc_of_selection ValiantBorder.polynomialImageArc h
  letI : CharZero K := charZero_of_injective_ringHom j.injective
  have hg := ValiantBorder.affineDetCircuit (fun (_ _ : Fin n) => (0 : LaurentSeries K))
    (fun i j t => v (i,j,t))
  have hsize : (Fintype.card (GCT.PadVars m)+n+2)^8 ≤ (m+n+2)^16 := by
    rw [show (16:ℕ) = 2 * 8 by decide,pow_mul]
    apply Nat.pow_le_pow_left
    simp [GCT.PadVars]
    ring_nf
    omega
  have hh : Statement.Computes (map (HahnSeries.ofPowerSeries ℤ K) Q) ((m+n+2)^16) := by
    rw [hdet]
    apply computes_widen _ hsize
    simpa [pencil,lin] using hg
  have dh := computes_dehomogenize hh
  rw [← map_dehomogenize] at dh
  have hp := of_regular_output (dehomogenize Q) dh
  rw [map_dehomogenize,hQ,← map_dehomogenize,dehomogenize_perm] at hp
  have hm : map j (Statement.perm ℂ m) = map (Int.castRingHom K) (Statement.perm ℤ m) := by
    simp only [Statement.perm,map_sum,map_prod,map_X]
  rw [hm] at hp
  obtain ⟨q,hq,hc⟩ := ValiantBorder.laurentTransfer (K:=ℂ) 0 (Statement.perm ℤ m) hp
  have H : BorderLaurent.Computes q ((m+n+2)^16) := hq
  refine ⟨map (BorderLaurent.laurentToSeries ℂ) q,H.map _,fun d i hi => ?_⟩
  rw [coeff_map,BorderLaurent.coeff_laurentToSeries]
  obtain hi | rfl := lt_or_eq_of_le hi
  · rw [if_neg hi.ne]; exact (hc d).1 i hi
  · rw [if_pos rfl]; simpa only [Statement.perm,map_sum,map_prod,map_X] using (hc d).2
