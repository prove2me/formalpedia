-- Prove2me | solution 1 for PhilipponMultiplicity.masser_wustholz_recovery
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-30T17:29:23.637678+00:00
-- url     : https://prove2.me/submissions/66e2803b-5340-4c02-8039-a845828b3b1f

import Theorems.Thm_PhilipponMultiplicity_masser_wustholz_geometric_coset_bound
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
open scoped BigOperators
open Submodule
noncomputable section

namespace PhilipponMultiplicity.MWLattice

def rationalVector {m : ℕ} : (Fin m → ℤ) →ₗ[ℤ] (Fin m → ℚ) where
  toFun v i := v i
  map_add' v w := by ext i; simp
  map_smul' c v := by ext i; simp

def integerCube (m : ℕ) (S : ℝ) : Set (Fin m → ℤ) :=
  {v | ∀ i, 0 ≤ v i ∧ (v i : ℝ) ≤ S}

theorem integerCube_finite (m : ℕ) (S : ℝ) : (integerCube m S).Finite := by
  apply (Set.Finite.pi (fun _ : Fin m =>
    (Set.finite_Icc (0 : ℤ) ⌊S⌋))).subset
  intro v hv i _
  exact ⟨(hv i).1, (Int.le_floor).mpr (hv i).2⟩

/-- Standard coordinate directions contain a basis of every rational quotient. -/
theorem coordinate_quotient_basis {m : ℕ} (W : Submodule ℚ (Fin m → ℚ)) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → Fin m), Function.Injective f ∧
      Fintype.card ι + Module.finrank ℚ W = m ∧
      LinearIndependent ℚ (fun i => W.mkQ (Pi.single (f i) 1)) := by
  classical
  let v (i : Fin m) := W.mkQ (Pi.single i 1)
  have hspan : span ℚ (Set.range v) = ⊤ := by
    have h := (Pi.basisFun ℚ (Fin m)).span_eq
    have hm := congrArg (Submodule.map W.mkQ) h
    simpa only [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
      LinearMap.range_eq_top.mpr W.mkQ_surjective, Function.comp_def,
      Pi.basisFun_apply, v] using hm
  obtain ⟨ι,f,hf,hsp,hli⟩ := exists_linearIndependent' ℚ v
  letI : Finite ι := Finite.of_injective f hf
  letI : Fintype ι := Fintype.ofFinite ι
  refine ⟨ι,inferInstance,f,hf,?_,hli⟩
  have hc := Module.finrank_eq_card_basis (Module.Basis.span hli)
  rw [hsp,hspan,finrank_top] at hc
  have hd := W.finrank_quotient_add_finrank
  simpa only [hc, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using hd

/-- A cube larger than its image produces a relation outside any prescribed
rational subspace, with no loss in the coordinate bound. -/
theorem short_relation_outside
    {M : Type*} [AddCommGroup M] {m : ℕ}
    (f : (Fin m → ℤ) →+ M) (W : Submodule ℚ (Fin m → ℚ))
    (B S : ℝ) (hB : 0 ≤ B) (hBS : B ≤ S)
    (hcard : (((f '' integerCube m S).ncard : ℕ) : ℝ) <
      ((⌊B⌋₊+1 : ℕ) : ℝ) ^ (m - Module.finrank ℚ W)) :
    ∃ v : Fin m → ℤ, f v = 0 ∧ rationalVector v ∉ W ∧
      ∀ i, |(v i : ℝ)| ≤ B := by
  classical
  obtain ⟨ι,inst,fidx,hidx,hdim,hlin⟩ := coordinate_quotient_basis W
  letI := inst
  let C := ι → Fin (⌊B⌋₊+1)
  let vec (a : C) : Fin m → ℤ := ∑ j, (a j).val • Pi.single (fidx j) (1 : ℤ)
  have heval (a : C) (j : ι) : vec a (fidx j) = (a j).val := by
    simp [vec, Finset.sum_apply, Pi.single_apply, hidx.eq_iff]
  have heval0 (a : C) (i : Fin m) (hi : i ∉ Set.range fidx) : vec a i = 0 := by
    have hh (j : ι) : fidx j ≠ i := fun h => hi ⟨j,h⟩
    simp [vec, Finset.sum_apply, Pi.single_apply, hh]
  have hvec (a : C) (i : Fin m) : 0 ≤ vec a i ∧ (vec a i : ℝ) ≤ B := by
    by_cases hi : i ∈ Set.range fidx
    · obtain ⟨j,rfl⟩ := hi
      rw [heval]
      constructor
      · positivity
      · exact_mod_cast (Nat.le_floor_iff hB).mp (Nat.le_of_lt_succ (a j).isLt)
    · rw [heval0 a i hi]
      simpa using hB
  let F (a : C) : f '' integerCube m S :=
    ⟨f (vec a),vec a,fun i => ⟨(hvec a i).1,(hvec a i).2.trans hBS⟩,rfl⟩
  letI : Fintype (f '' integerCube m S) :=
    ((integerCube_finite m S).image f).fintype
  have hdim' : Fintype.card ι = m - Module.finrank ℚ W := by omega
  have hc : Fintype.card (f '' integerCube m S) < Fintype.card C := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card] at hcard
    simp only [C, Fintype.card_fun, Fintype.card_fin, hdim']
    exact_mod_cast hcard
  obtain ⟨a,b,hab,hFab⟩ := Fintype.exists_ne_map_eq_of_card_lt F hc
  have hf : f (vec a) = f (vec b) := congrArg Subtype.val hFab
  refine ⟨vec a - vec b,by rw [map_sub,hf,sub_self],?_,?_⟩
  · intro hmem
    apply hab
    have hq : W.mkQ (rationalVector (vec a)) = W.mkQ (rationalVector (vec b)) := by
      apply sub_eq_zero.mp
      rw [← map_sub, ← map_sub]
      exact (Submodule.Quotient.mk_eq_zero W).mpr hmem
    have hcast (c : C) : rationalVector (vec c) =
        ∑ j, ((c j).val : ℚ) • Pi.single (fidx j) 1 := by
      ext i
      simp [rationalVector, vec, Finset.sum_apply, Pi.single_apply]
    rw [hcast,hcast,map_sum,map_sum] at hq
    simp only [map_smul] at hq
    have hab' := hlin.fintypeLinearCombination_injective hq
    funext j
    apply Fin.ext
    exact_mod_cast congrFun hab' j
  · intro i
    have ha := hvec a i
    have hb := hvec b i
    change |((vec a i - vec b i : ℤ) : ℝ)| ≤ B
    rw [Int.cast_sub,abs_le]
    have ha0 : (0 : ℝ) ≤ vec a i := by exact_mod_cast ha.1
    have hb0 : (0 : ℝ) ≤ vec b i := by exact_mod_cast hb.1
    constructor <;> linarith

/-- Iterated pigeonhole counting supplies the different bounds on successive
independent relations. The quotient need not be torsion-free. -/
theorem independent_relations_up_to
    {M : Type*} [AddCommGroup M] {m r : ℕ}
    (f : (Fin m → ℤ) →+ M) (X θ : ℝ) (hX : 1 ≤ X)
    (hcount : ((f '' integerCube m (X ^ θ)).ncard : ℝ) ≤ X ^ r)
    (k : ℕ) (hk : k ≤ m)
    (hexponents : ∀ j < k, (r : ℝ) / ((m : ℝ) - j) ≤ θ) :
    ∃ σ : Fin k → (Fin m → ℤ),
      (∀ j, f (σ j) = 0) ∧
      LinearIndependent ℚ (fun j => rationalVector (σ j)) ∧
      ∀ j : Fin k, ∀ i : Fin m,
        |(σ j i : ℝ)| ≤ X ^ ((r : ℝ) / ((m : ℝ) - j.val)) := by
  induction k with
  | zero =>
    refine ⟨Fin.elim0,fun j => Fin.elim0 j,?_,fun j => Fin.elim0 j⟩
    exact linearIndependent_empty_type
  | succ k ih =>
    obtain ⟨σ,hσ,hlin,hbound⟩ := ih (by omega) (fun j hj => hexponents j (by omega))
    let W := span ℚ (Set.range (fun j => rationalVector (σ j)))
    have hW : Module.finrank ℚ W = k := by
      simpa only [W,Fintype.card_fin] using finrank_span_eq_card hlin
    have hkm : k < m := by omega
    have hden : 0 < (m : ℝ) - k := sub_pos.mpr (by exact_mod_cast hkm)
    let B : ℝ := X ^ ((r : ℝ) / ((m : ℝ) - k))
    have hB : 0 < B := Real.rpow_pos_of_pos (by linarith) _
    have hBS : B ≤ X ^ θ := Real.rpow_le_rpow_of_exponent_le hX
      (hexponents k (by omega))
    have hpower : B ^ (m-k) = X ^ r := by
      dsimp only [B]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ X),
        Nat.cast_sub (by omega : k ≤ m), div_mul_cancel₀ _ hden.ne']
      exact Real.rpow_natCast X r
    have hstrict : X ^ r < ((⌊B⌋₊+1 : ℕ) : ℝ) ^ (m-k) := by
      rw [← hpower]
      apply pow_lt_pow_left₀ (by exact_mod_cast Nat.lt_floor_add_one B) hB.le
      omega
    obtain ⟨v,hv,hvW,hvbound⟩ := short_relation_outside f W B (X ^ θ) hB.le hBS
      (by rw [hW]; exact hcount.trans_lt hstrict)
    have hcast : (fun j : Fin (k+1) => rationalVector
        ((Fin.snoc σ v : Fin (k+1) → (Fin m → ℤ)) j)) =
        Fin.snoc (fun j => rationalVector (σ j)) (rationalVector v) := by
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
    refine ⟨Fin.snoc σ v,?_,?_,?_⟩
    · intro j
      exact Fin.lastCases (by simpa using hv) (fun i => by simpa using hσ i) j
    · rw [hcast]
      exact hlin.finSnoc hvW
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [Fin.snoc_last,Fin.val_last] using hvbound
      · simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using hbound i

/-- The least integer crossing the rank threshold is positive and at most m;
all preceding pigeonhole cubes fit inside the original sampling cube. -/
theorem threshold_index (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r)
    (θ : ℝ) (hθ : (r : ℝ) / m ≤ θ) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ (m : ℝ) < k + (r : ℝ) / θ ∧
      ∀ j < k, (r : ℝ) / ((m : ℝ) - j) ≤ θ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have ht : 0 < θ := (div_pos hrR hmR).trans_le hθ
  have hex : ∃ k : ℕ, (m : ℝ) < k + (r : ℝ) / θ :=
    ⟨m,by linarith [div_pos hrR ht]⟩
  let k := Nat.find hex
  have hk : (m : ℝ) < k + (r : ℝ) / θ := Nat.find_spec hex
  have hkm : k ≤ m := Nat.find_min' hex (by linarith [div_pos hrR ht])
  have hkpos : 1 ≤ k := by
    by_contra h
    have hz : k = 0 := by omega
    rw [hz,Nat.cast_zero,zero_add] at hk
    have h1 := (lt_div_iff₀ ht).mp hk
    have h2 := (div_le_iff₀ hmR).mp hθ
    nlinarith
  refine ⟨k,hkpos,hkm,hk,?_⟩
  intro j hj
  have hjm : j < m := lt_of_lt_of_le hj hkm
  have hden : 0 < (m : ℝ) - j := sub_pos.mpr (by exact_mod_cast hjm)
  have hmin : (j : ℝ) + (r : ℝ) / θ ≤ m := le_of_not_gt (Nat.find_min hex hj)
  apply (div_le_iff₀ hden).mpr
  have hdiv : (r : ℝ) / θ ≤ (m : ℝ) - j := by linarith
  have hh := (div_le_iff₀ ht).mp hdiv
  nlinarith

/-- A finite quotient of an integer cube yields all lattice conclusions of
Masser--Wüstholz, with the exact coordinate bounds and strict rank inequality. -/
theorem relations_of_cube_image_bound
    {M : Type*} [AddCommGroup M] {m r : ℕ}
    (f : (Fin m → ℤ) →+ M) (hm : 1 ≤ m) (hr : 1 ≤ r)
    (X θ : ℝ) (hX : 1 ≤ X) (hθ : (r : ℝ) / m ≤ θ)
    (hcount : ((f '' integerCube m (X ^ θ)).ncard : ℝ) ≤ X ^ r) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ (m : ℝ) < k + (r : ℝ) / θ ∧
      ∃ σ : Fin k → LinearMap.ker f.toIntLinearMap,
        k ≤ Module.finrank ℤ (LinearMap.ker f.toIntLinearMap) ∧
        LinearIndependent ℤ (fun j => (σ j).val) ∧
        ∀ j : Fin k, ∀ i : Fin m,
          |((σ j).val i : ℝ)| ≤ X ^ ((r : ℝ) / ((m : ℝ) - j.val)) := by
  obtain ⟨k,hk,hkm,hstrict,hexp⟩ := threshold_index m r hm hr θ hθ
  obtain ⟨σ,hσ,hlin,hbound⟩ := independent_relations_up_to f X θ hX hcount k hkm hexp
  have hZ : LinearIndependent ℤ σ := LinearIndependent.of_comp rationalVector
    (hlin.restrict_scalars' ℤ)
  let τ (j : Fin k) : LinearMap.ker f.toIntLinearMap := ⟨σ j,hσ j⟩
  have hτ : LinearIndependent ℤ τ :=
    LinearIndependent.of_comp (LinearMap.ker f.toIntLinearMap).subtype hZ
  refine ⟨k,hk,hkm,hstrict,τ,?_,hZ,hbound⟩
  simpa only [Fintype.card_fin] using hτ.fintype_card_le_finrank

def combinationHom {K : Type*} [Field K] {G : EmbeddedGroupProduct K}
    {m : ℕ} (γ : Fin m → G.Point) : (Fin m → ℤ) →+ G.Point where
  toFun := integerCombination γ
  map_zero' := by simp [integerCombination]
  map_add' a b := by simp [integerCombination,add_zsmul,Finset.sum_add_distrib]

theorem integerCube_image_eq_grid {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}
    {m : ℕ} (γ : Fin m → G.Point) (S : ℝ) :
    combinationHom γ '' integerCube m S = samplingGrid γ S := by
  ext x
  constructor
  · rintro ⟨v,hv,rfl⟩
    refine ⟨fun i => (v i).toNat,?_,?_⟩
    · intro i
      have heq : ((v i).toNat : ℝ) = (v i : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (hv i).1
      rw [heq]
      exact (hv i).2
    · change (∑ i, (v i) • γ i) = ∑ i, (v i).toNat • γ i
      apply Finset.sum_congr rfl
      intro i _
      calc
        (v i) • γ i = ((v i).toNat : ℤ) • γ i := by
          rw [Int.toNat_of_nonneg (hv i).1]
        _ = (v i).toNat • γ i := natCast_zsmul _ _
  · rintro ⟨a,ha,rfl⟩
    refine ⟨fun i => (a i : ℤ),fun i => ⟨by positivity,by exact_mod_cast ha i⟩,?_⟩
    change (∑ i, (a i : ℤ) • γ i) = ∑ i, a i • γ i
    simp only [natCast_zsmul]

/-- Identify cosets with fibers of the quotient map; no torsion-free assumption. -/
theorem quotient_image_ncard {M : Type*} [AddCommGroup M]
    (H : AddSubgroup M) (S : Set M) :
    ((QuotientAddGroup.mk' H) '' S).ncard =
      (((fun x => (fun y => x+y) '' (H : Set M))) '' S).ncard := by
  let q := QuotientAddGroup.mk' H
  let fiber (z : M ⧸ H) : Set M := q ⁻¹' {z}
  have hf : Function.Injective fiber := by
    intro x y h
    obtain ⟨a,rfl⟩ := QuotientAddGroup.mk_surjective x
    have ha : a ∈ fiber (q a) := rfl
    change fiber (q a) = fiber y at h
    rw [h] at ha
    exact ha
  have hcoset (x : M) : (fun y => x+y) '' (H : Set M) = fiber (q x) := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      change q (x+z) = q x
      rw [map_add,show q z = 0 from (QuotientAddGroup.eq_zero_iff z).mpr hz,add_zero]
    · intro hy
      have hz : y-x ∈ H := (QuotientAddGroup.eq_zero_iff (y-x)).mp (by
        change q (y-x) = 0
        rw [map_sub,show q y = q x from hy,sub_self])
      exact ⟨y-x,hz,by abel_nf⟩
  simp_rw [hcoset]
  change (q '' S).ncard = ((fiber ∘ q) '' S).ncard
  simp only [Function.comp_def]
  rw [← Set.image_image fiber q S,Set.ncard_image_of_injective _ hf]

/-- The complete lattice output attached to a geometric grid-coset estimate. -/
theorem relations_of_grid_coset_bound
    {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K} {m r : ℕ}
    (γ : Fin m → G.Point) (H : AlgebraicSubgroup G)
    (hm : 1 ≤ m) (hr : 1 ≤ r) (X θ : ℝ) (hX : 1 ≤ X)
    (hθ : (r : ℝ) / m ≤ θ)
    (hcount : (((fun g => PhilipponMultiplicity.translate g H.carrier) ''
      samplingGrid γ (X ^ θ)).ncard : ℝ) ≤ X ^ r) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ (m : ℝ) < k + (r : ℝ) / θ ∧
      ∃ Z : Submodule ℤ (Fin m → ℤ), k ≤ Module.finrank ℤ Z ∧
        (∀ v ∈ Z, integerCombination γ v ∈ H.carrier) ∧
        ∃ σ : Fin k → Z,
          LinearIndependent ℤ (fun j => (σ j).val) ∧
          ∀ j : Fin k, ∀ i : Fin m,
            |((σ j).val i : ℝ)| ≤ X ^ ((r : ℝ) / ((m : ℝ) - j.val)) := by
  let f := (QuotientAddGroup.mk' H.toAddSubgroup).comp (combinationHom γ)
  have hc : ((f '' integerCube m (X ^ θ)).ncard : ℝ) ≤ X ^ r := by
    change (((QuotientAddGroup.mk' H.toAddSubgroup ∘ combinationHom γ) ''
      integerCube m (X ^ θ)).ncard : ℝ) ≤ _
    simp only [Function.comp_def]
    rw [← Set.image_image (QuotientAddGroup.mk' H.toAddSubgroup) (combinationHom γ)
      (integerCube m (X ^ θ)),integerCube_image_eq_grid,quotient_image_ncard]
    exact hcount
  obtain ⟨k,hk,hkm,hstrict,σ,hrank,hlin,hbound⟩ :=
    relations_of_cube_image_bound f hm hr X θ hX hθ hc
  refine ⟨k,hk,hkm,hstrict,LinearMap.ker f.toIntLinearMap,hrank,?_,σ,hlin,hbound⟩
  intro v hv
  exact (QuotientAddGroup.eq_zero_iff _).mp hv

end PhilipponMultiplicity.MWLattice

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MWLattice

theorem constant_bounds (a b D n e : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hD : 1 ≤ D) :
    let c : ℝ := 1 / ((a : ℝ)^n * (b : ℝ)^e)
    0 < c ∧ c ≤ 1 ∧ 1 ≤ (D : ℝ) / c ∧ (a : ℝ)^n * D ≤ (D : ℝ) / c := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hA : 1 ≤ (a : ℝ)^n := one_le_pow₀ haR
  have hB : 1 ≤ (b : ℝ)^e := one_le_pow₀ hbR
  have hAB : 1 ≤ (a : ℝ)^n * (b : ℝ)^e := one_le_mul_of_one_le_of_one_le hA hB
  dsimp only
  refine ⟨one_div_pos.mpr (by linarith), (div_le_one (by linarith)).mpr hAB,?_,?_⟩
  · simp only [one_div,div_inv_eq_mul]
    exact one_le_mul_of_one_le_of_one_le hDR hAB
  · simp only [one_div,div_inv_eq_mul]
    calc
      (a : ℝ)^n * D ≤ ((a : ℝ)^n * D) * (b : ℝ)^e :=
        le_mul_of_one_le_right (mul_nonneg (by positivity) (by positivity)) hB
      _ = (D : ℝ) * ((a : ℝ)^n * (b : ℝ)^e) := by ring

theorem equations_bound_mono {K : Type*} [Field K] {G : EmbeddedGroupProduct K}
    {V : Set G.Point} {B C : ℝ} (h : DefinedByEquations G V B) (hBC : B ≤ C) :
    DefinedByEquations G V C := by
  obtain ⟨eqs,heqs,hV⟩ := h
  refine ⟨eqs,?_,hV⟩
  intro P hP
  obtain ⟨D,hD,hbound⟩ := heqs P hP
  exact ⟨D,hD,fun i => (hbound i).trans hBC⟩

end PhilipponMultiplicity.MWLattice

namespace PhilipponMultiplicity
universe u

theorem recovery_of_geometric_coset_bound
    (hgeometry : ∀
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (E : EmbeddedCommutativeGroup K)
    (hn : 0 < (singleGroupProduct E).dimension)
    (hconnected : @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (htranslation : MWTranslationBound (singleGroupProduct E) a)
    (hclosure : ∃ equations : Finset (singleGroupProduct E).CoordinateRing,
      (∀ P ∈ equations, (singleGroupProduct E).ambient.IsHomogeneousAtMost P (fun _ => b)) ∧
      groupProjectiveClosure (singleGroupProduct E) =
        {x | ∀ P ∈ equations, (singleGroupProduct E).ambient.eval P x = 0})
    (m D : ℕ) (hm : 1 ≤ m) (hD : 1 ≤ D)
    (γ : Fin m → (singleGroupProduct E).Point) (R : ℝ) (hR : 1 ≤ R)
    (P : (singleGroupProduct E).CoordinateRing)
    (hP : (singleGroupProduct E).ambient.IsHomogeneousAtMost P (fun _ => D)),
    let G := singleGroupProduct E
    let c : ℝ := 1 / ((a : ℝ) ^ G.dimension * (b : ℝ) ^ (E.ambientDimension - G.dimension))
    (∀ x ∈ samplingGrid γ ((G.dimension : ℝ) * R),
      G.ambient.eval P (G.embedding x) = 0) →
    (∃ x : G.Point, G.ambient.eval P (G.embedding x) ≠ 0) →
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ G.dimension ∧
      ∃ H : AlgebraicSubgroup G, varietyDimension G H.carrier ≤ G.dimension - r ∧
        ((((fun g => translate g H.carrier) '' samplingGrid γ R).ncard : ℝ) ≤
          ((D : ℝ) / c) ^ r) ∧
        ∃ V : GroupSubvariety G, H.carrier ⊆ V.carrier ∧
          varietyDimension G V.carrier ≤ G.dimension - r ∧
          DefinedByEquations G V.carrier ((a : ℝ) ^ G.dimension * (D : ℝ)))
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (E : EmbeddedCommutativeGroup K)
    (hn : 0 < (singleGroupProduct E).dimension)
    (hconnected : @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (htranslation : MWTranslationBound (singleGroupProduct E) a)
    (hclosure : ∃ equations : Finset (singleGroupProduct E).CoordinateRing,
      (∀ P ∈ equations, (singleGroupProduct E).ambient.IsHomogeneousAtMost P (fun _ => b)) ∧
      groupProjectiveClosure (singleGroupProduct E) =
        {x | ∀ P ∈ equations, (singleGroupProduct E).ambient.eval P x = 0})
    (m D : ℕ) (hm : 1 ≤ m) (hD : 1 ≤ D)
    (γ : Fin m → (singleGroupProduct E).Point) (θ : ℝ)
    (hθ : ((singleGroupProduct E).dimension : ℝ) / m ≤ θ)
    (P : (singleGroupProduct E).CoordinateRing)
    (hP : (singleGroupProduct E).ambient.IsHomogeneousAtMost P (fun _ => D)) :
    let G := singleGroupProduct E
    let c : ℝ := 1 / ((a : ℝ) ^ G.dimension * (b : ℝ) ^ (E.ambientDimension - G.dimension))
    (∀ x ∈ samplingGrid γ ((G.dimension : ℝ) * ((D : ℝ) / c) ^ θ),
      G.ambient.eval P (G.embedding x) = 0) →
    (∃ x : G.Point, G.ambient.eval P (G.embedding x) ≠ 0) →
    ∃ k r : ℕ, 1 ≤ k ∧ k ≤ m ∧ 1 ≤ r ∧ r ≤ G.dimension ∧
      (m : ℝ) < (k : ℝ) + (r : ℝ) / θ ∧
      ∃ Z : Submodule ℤ (Fin m → ℤ), k ≤ Module.finrank ℤ Z ∧
      ∃ H : AlgebraicSubgroup G, varietyDimension G H.carrier ≤ G.dimension - r ∧
        (∀ σ ∈ Z, integerCombination γ σ ∈ H.carrier) ∧
        (∃ σ : Fin k → Z,
          LinearIndependent ℤ (fun j => (σ j).val) ∧
          ∀ j : Fin k, ∀ i : Fin m,
            |((σ j).val i : ℝ)| ≤ ((D : ℝ) / c) ^ ((r : ℝ) / ((m : ℝ) - j.val))) ∧
        ∃ S : GroupSubvariety G, H.carrier ⊆ S.carrier ∧
          varietyDimension G S.carrier ≤ G.dimension - r ∧
          DefinedByEquations G S.carrier ((D : ℝ) / c) := by
  dsimp only
  intro hvanish hnonzero
  let G := singleGroupProduct E
  let c : ℝ := 1 / ((a : ℝ)^G.dimension * (b : ℝ)^(E.ambientDimension-G.dimension))
  let X : ℝ := (D : ℝ) / c
  obtain ⟨hcpos,hcle,hX,hdegree⟩ := MWLattice.constant_bounds a b D G.dimension
    (E.ambientDimension-G.dimension) ha hb hD
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnR : (0 : ℝ) < G.dimension := by exact_mod_cast hn
  have ht : 0 < θ := (div_pos hnR hmR).trans_le hθ
  have hR : 1 ≤ X ^ θ := Real.one_le_rpow hX ht.le
  obtain ⟨r,hr,hrn,H,hH,hcount,V,hHV,hVdim,hVeq⟩ :=
    hgeometry K hK E hn hconnected a b ha hb htranslation hclosure m D hm hD
      γ (X ^ θ) hR P hP hvanish hnonzero
  have hrt : (r : ℝ) / m ≤ θ :=
    (div_le_div_of_nonneg_right (by exact_mod_cast hrn) (Nat.cast_nonneg m)).trans hθ
  obtain ⟨k,hk,hkm,hstrict,Z,hrank,hZ,σ,hlin,hbound⟩ :=
    MWLattice.relations_of_grid_coset_bound γ H hm hr X θ hX hrt hcount
  exact ⟨k,r,hk,hkm,hr,hrn,hstrict,Z,hrank,H,hH,hZ,⟨σ,hlin,hbound⟩,
    V,hHV,hVdim,MWLattice.equations_bound_mono hVeq hdegree⟩

end PhilipponMultiplicity

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (E : EmbeddedCommutativeGroup K)
    (hn : 0 < (singleGroupProduct E).dimension)
    (hconnected : @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (htranslation : MWTranslationBound (singleGroupProduct E) a)
    (hclosure : ∃ equations : Finset (singleGroupProduct E).CoordinateRing,
      (∀ P ∈ equations, (singleGroupProduct E).ambient.IsHomogeneousAtMost P (fun _ => b)) ∧
      groupProjectiveClosure (singleGroupProduct E) =
        {x | ∀ P ∈ equations, (singleGroupProduct E).ambient.eval P x = 0})
    (m D : ℕ) (hm : 1 ≤ m) (hD : 1 ≤ D)
    (γ : Fin m → (singleGroupProduct E).Point) (θ : ℝ)
    (hθ : ((singleGroupProduct E).dimension : ℝ) / m ≤ θ)
    (P : (singleGroupProduct E).CoordinateRing)
    (hP : (singleGroupProduct E).ambient.IsHomogeneousAtMost P (fun _ => D)) :
    let G := singleGroupProduct E
    let c : ℝ := 1 / ((a : ℝ) ^ G.dimension * (b : ℝ) ^ (E.ambientDimension - G.dimension))
    (∀ x ∈ samplingGrid γ ((G.dimension : ℝ) * ((D : ℝ) / c) ^ θ),
      G.ambient.eval P (G.embedding x) = 0) →
    (∃ x : G.Point, G.ambient.eval P (G.embedding x) ≠ 0) →
    ∃ k r : ℕ, 1 ≤ k ∧ k ≤ m ∧ 1 ≤ r ∧ r ≤ G.dimension ∧
      (m : ℝ) < (k : ℝ) + (r : ℝ) / θ ∧
      ∃ Z : Submodule ℤ (Fin m → ℤ), k ≤ Module.finrank ℤ Z ∧
      ∃ H : AlgebraicSubgroup G, varietyDimension G H.carrier ≤ G.dimension - r ∧
        (∀ σ ∈ Z, integerCombination γ σ ∈ H.carrier) ∧
        (∃ σ : Fin k → Z,
          LinearIndependent ℤ (fun j => (σ j).val) ∧
          ∀ j : Fin k, ∀ i : Fin m,
            |((σ j).val i : ℝ)| ≤ ((D : ℝ) / c) ^ ((r : ℝ) / ((m : ℝ) - j.val))) ∧
        ∃ S : GroupSubvariety G, H.carrier ⊆ S.carrier ∧
          varietyDimension G S.carrier ≤ G.dimension - r ∧
          DefinedByEquations G S.carrier ((D : ℝ) / c) := by
  exact recovery_of_geometric_coset_bound
    (@masser_wustholz_geometric_coset_bound) K hK E hn hconnected a b ha hb
    htranslation hclosure m D hm hD γ θ hθ P hP
