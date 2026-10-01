-- Prove2me | solution 1 for PhilipponMultiplicity.masser_wustholz_local_prime_estimate
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-30T18:55:50.76419+00:00
-- url     : https://prove2.me/submissions/0a39466d-4e48-470b-a9e4-384ac4e14f5f

import Theorems.Thm_PhilipponMultiplicity_masser_wustholz_pointed_prime_orbit
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_SectionFive
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

section
-- Reused implementation: Solutions.PhilipponMasserWustholzLattice

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
end
end


section
-- Reused implementation: Solutions.PhilipponMasserWustholzRelations

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Pointwise
noncomputable section

namespace PhilipponMultiplicity.MWRelations

/-- Maps with the same fibers on a set have equally many image points. -/
theorem image_ncard_eq_of_fibers {X Y Z : Type*} (S : Set X) (f : X → Y) (g : X → Z)
    (h : ∀ x ∈ S, ∀ y ∈ S, f x = f y ↔ g x = g y) :
    (f '' S).ncard = (g '' S).ncard := by
  classical
  choose rep hrep heq using fun y : f '' S => y.property
  let F (y : f '' S) : g '' S := ⟨g (rep y),rep y,hrep y,rfl⟩
  apply Set.ncard_congr' (Equiv.ofBijective F ?_)
  constructor
  · intro y z hyz
    apply Subtype.ext
    have hg : g (rep y) = g (rep z) := congrArg Subtype.val hyz
    exact (heq y).symm.trans (((h _ (hrep y) _ (hrep z)).mpr hg).trans (heq z))
  · rintro ⟨_,x,hx,rfl⟩
    let y : f '' S := ⟨f x,x,hx,rfl⟩
    refine ⟨y,Subtype.ext ?_⟩
    exact (h (rep y) (hrep y) x hx).mp (heq y)

variable {M : Type*} [AddCommGroup M]

theorem translate_comp (x y : M) (W : Set M) :
    translate x (translate y W) = translate (x+y) W := by
  simp only [translate,Set.image_image,Function.comp_def,add_assoc]

theorem translate_zero (W : Set M) : translate (0 : M) W = W := by
  simp only [translate,zero_add,Set.image_id']

theorem translate_eq_iff_sub_mem (W : Set M) (x y : M) :
    translate x W = translate y W ↔ x-y ∈ AddAction.stabilizer M W := by
  constructor
  · intro h
    change translate (x-y) W = W
    calc
      translate (x-y) W = translate (-y) (translate x W) := by
        rw [translate_comp]
        congr 1
        abel
      _ = translate (-y) (translate y W) := by rw [h]
      _ = W := by rw [translate_comp,neg_add_cancel,translate_zero]
  · intro h
    change translate (x-y) W = W at h
    calc
      translate x W = translate y (translate (x-y) W) := by
        rw [translate_comp]
        congr 1
        abel
      _ = translate y W := by rw [h]

/-- All differences between equivalent points of the integer cube generate
a subgroup with exactly the same sampled classes as the translation orbit. -/
theorem bounded_relations_of_pointed_orbit {m : ℕ}
    (f : (Fin m → ℤ) →+ M) (R : ℝ) (W : Set M) (h0 : 0 ∈ W) :
    ∃ relations : Finset (Fin m → ℤ),
      (∀ v ∈ relations, ∀ i, |(v i : ℝ)| ≤ R) ∧
      let A := (Submodule.span ℤ (f '' (relations : Set (Fin m → ℤ)))).toAddSubgroup
      (A : Set M) ⊆ W ∧
      ((fun g => translate g (A : Set M)) '' (f '' MWLattice.integerCube m R)).ncard =
        ((fun g => translate g W) '' (f '' MWLattice.integerCube m R)).ncard := by
  classical
  let C := (MWLattice.integerCube_finite m R).toFinset
  let pairs := (C.product C).filter
    (fun p => translate (f p.1) W = translate (f p.2) W)
  let relations := pairs.image (fun p => p.1-p.2)
  have hrelation (u v : Fin m → ℤ) : u-v ∈ relations ↔
      ∃ x ∈ MWLattice.integerCube m R, ∃ y ∈ MWLattice.integerCube m R,
        translate (f x) W = translate (f y) W ∧ x-y = u-v := by
    simp only [relations,pairs,Finset.mem_image,Finset.mem_filter,Finset.mem_product,
      C,Set.Finite.mem_toFinset,Prod.exists]
    aesop
  have hmem (v : Fin m → ℤ) (hv : v ∈ relations) :
      ∃ x ∈ MWLattice.integerCube m R, ∃ y ∈ MWLattice.integerCube m R,
        translate (f x) W = translate (f y) W ∧ x-y = v := by
    simpa only [sub_zero] using (hrelation v 0).mp (by simpa only [sub_zero] using hv)
  let A := (Submodule.span ℤ (f '' (relations : Set (Fin m → ℤ)))).toAddSubgroup
  have hAT : A ≤ AddAction.stabilizer M W := by
    change Submodule.span ℤ (f '' (relations : Set (Fin m → ℤ))) ≤
      (AddAction.stabilizer M W).toIntSubmodule
    apply Submodule.span_le.mpr
    rintro _ ⟨v,hv,rfl⟩
    obtain ⟨x,hx,y,hy,heq,rfl⟩ := hmem v hv
    rw [map_sub]
    exact (translate_eq_iff_sub_mem W _ _).mp heq
  have hAV : (A : Set M) ⊆ W := by
    intro x hx
    have hh : translate x W = W := hAT hx
    rw [← hh]
    exact ⟨0,h0,add_zero x⟩
  refine ⟨relations,?_,hAV,?_⟩
  · intro v hv i
    obtain ⟨x,hx,y,hy,_,rfl⟩ := hmem v hv
    simp only [Pi.sub_apply,Int.cast_sub,abs_le]
    have hx0 : (0 : ℝ) ≤ x i := by exact_mod_cast (hx i).1
    have hy0 : (0 : ℝ) ≤ y i := by exact_mod_cast (hy i).1
    constructor <;> linarith [(hx i).2,(hy i).2]
  · let q := QuotientAddGroup.mk' A
    have hfib (x : Fin m → ℤ) (hx : x ∈ MWLattice.integerCube m R)
        (y : Fin m → ℤ) (hy : y ∈ MWLattice.integerCube m R) :
        q (f x) = q (f y) ↔ translate (f x) W = translate (f y) W := by
      constructor
      · intro h
        apply (translate_eq_iff_sub_mem W _ _).mpr
        apply hAT
        apply (QuotientAddGroup.eq_zero_iff (f x-f y)).mp
        change q (f x-f y) = 0
        rw [map_sub,h,sub_self]
      · intro h
        have hrel : x-y ∈ relations := (hrelation x y).mpr ⟨x,hx,y,hy,h,rfl⟩
        have hA : f (x-y) ∈ A := Submodule.subset_span ⟨x-y,hrel,rfl⟩
        have hz := (QuotientAddGroup.eq_zero_iff (f (x-y))).mpr hA
        change q (f (x-y)) = 0 at hz
        rwa [map_sub,map_sub,sub_eq_zero] at hz
    have hc := image_ncard_eq_of_fibers (MWLattice.integerCube m R)
      (fun x => q (f x)) (fun x => translate (f x) W) hfib
    rw [← Set.image_image q f,← Set.image_image (fun x => translate x W) f] at hc
    rw [MWLattice.quotient_image_ncard] at hc
    exact hc

theorem bounded_relations_of_sampling_orbit
    {K : Type*} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K} {m : ℕ}
    (γ : Fin m → G.Point) (R : ℝ) (W : Set G.Point) (h0 : 0 ∈ W) :
    ∃ relations : Finset (Fin m → ℤ),
      (∀ v ∈ relations, ∀ i, |(v i : ℝ)| ≤ R) ∧
      let A := (Submodule.span ℤ
        (integerCombination γ '' (relations : Set (Fin m → ℤ)))).toAddSubgroup
      (A : Set G.Point) ⊆ W ∧
      ((fun g => translate g (A : Set G.Point)) '' samplingGrid γ R).ncard =
        ((fun g => translate g W) '' samplingGrid γ R).ncard := by
  have h := bounded_relations_of_pointed_orbit (MWLattice.combinationHom γ) R W h0
  simp only [MWLattice.integerCube_image_eq_grid] at h
  simpa only [MWLattice.combinationHom,AddMonoidHom.coe_mk,ZeroHom.coe_mk] using h

end PhilipponMultiplicity.MWRelations

end
end


section
-- Reused implementation: Solutions.PhilipponMasserWustholzLocalAssembly
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
universe u

theorem local_prime_estimate_of_pointed_prime_orbit
    (horbit : ∀
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
    ∀ Γ : Submodule ℤ G.Point, Γ.FG → (∀ i, γ i ∈ Γ) →
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ G.dimension ∧
      ∃ p : Ideal G.CoordinateRing, p.IsPrime ∧ IsMultihomogeneousIdeal G.ambient p ∧
        G.vanishingIdeal Set.univ ≤ p ∧
        (0 : G.Point) ∈ idealZeroLocusOnGroup G p ∧
        ((((fun g => translate g (idealZeroLocusOnGroup G p)) '' samplingGrid γ R).ncard : ℝ) ≤
          ((D : ℝ) / c) ^ r) ∧
        ∃ Q : Finset G.CoordinateRing,
          (∀ F ∈ Q, ∃ d : G.FactorIndex → ℕ,
            G.ambient.IsHomogeneous F d ∧
              ∀ i, (d i : ℝ) ≤ (a : ℝ) ^ G.dimension * (D : ℝ)) ∧
          (∀ F ∈ Q, F ∈ p) ∧
          ∀ q ∈ (G.vanishingIdeal Set.univ ⊔ Ideal.span (Q : Set G.CoordinateRing)).minimalPrimes,
            (∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G q) →
            varietyDimension G (idealZeroLocusOnGroup G q) ≤ G.dimension - r)
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
    (hP : (singleGroupProduct E).ambient.IsHomogeneousAtMost P (fun _ => D)) :
    let G := singleGroupProduct E
    let c : ℝ := 1 / ((a : ℝ) ^ G.dimension * (b : ℝ) ^ (E.ambientDimension - G.dimension))
    (∀ x ∈ samplingGrid γ ((G.dimension : ℝ) * R),
      G.ambient.eval P (G.embedding x) = 0) →
    (∃ x : G.Point, G.ambient.eval P (G.embedding x) ≠ 0) →
    ∀ Γ : Submodule ℤ G.Point, Γ.FG → (∀ i, γ i ∈ Γ) →
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ G.dimension ∧
      ∃ relations : Finset (Fin m → ℤ), (∀ v ∈ relations, ∀ i, |(v i : ℝ)| ≤ R) ∧
        let A := (Submodule.span ℤ
          (integerCombination γ '' (relations : Set (Fin m → ℤ)))).toAddSubgroup
        ((((fun g => translate g (A : Set G.Point)) '' samplingGrid γ R).ncard : ℝ) ≤
          ((D : ℝ) / c) ^ r) ∧
        ∃ Q : Finset G.CoordinateRing,
          (∀ F ∈ Q, ∃ d : G.FactorIndex → ℕ,
            G.ambient.IsHomogeneous F d ∧
              ∀ i, (d i : ℝ) ≤ (a : ℝ) ^ G.dimension * (D : ℝ)) ∧
          (∀ x ∈ A, ∀ F ∈ Q, G.ambient.eval F (G.embedding x) = 0) ∧
          ∀ q ∈ (G.vanishingIdeal Set.univ ⊔ Ideal.span (Q : Set G.CoordinateRing)).minimalPrimes,
            (∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G q) →
            varietyDimension G (idealZeroLocusOnGroup G q) ≤ G.dimension - r := by
  dsimp only
  intro hvanish hnonzero Γ hΓ hγ
  obtain ⟨r,hr,hrn,p,hprime,hhom,hGp,hzero,hcount,Q,hQ,hQp,hdim⟩ :=
    horbit K hK E hn hconnected a b ha hb htranslation hclosure m D hm hD
      γ R hR P hP hvanish hnonzero Γ hΓ hγ
  obtain ⟨relations,hbound,hA,hclasses⟩ :=
    MWRelations.bounded_relations_of_sampling_orbit γ R
      (idealZeroLocusOnGroup (singleGroupProduct E) p) hzero
  refine ⟨r,hr,hrn,relations,hbound,?_,Q,hQ,?_,hdim⟩
  · exact (congrArg (fun t : ℕ => (t : ℝ)) hclasses).le.trans hcount
  · intro x hx F hF
    exact hA hx F (hQp F hF)

end PhilipponMultiplicity
end
end

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
    (γ : Fin m → (singleGroupProduct E).Point) (R : ℝ) (hR : 1 ≤ R)
    (P : (singleGroupProduct E).CoordinateRing)
    (hP : (singleGroupProduct E).ambient.IsHomogeneousAtMost P (fun _ => D)) :
    let G := singleGroupProduct E
    let c : ℝ := 1 / ((a : ℝ) ^ G.dimension * (b : ℝ) ^ (E.ambientDimension - G.dimension))
    (∀ x ∈ samplingGrid γ ((G.dimension : ℝ) * R),
      G.ambient.eval P (G.embedding x) = 0) →
    (∃ x : G.Point, G.ambient.eval P (G.embedding x) ≠ 0) →
    ∀ Γ : Submodule ℤ G.Point, Γ.FG → (∀ i, γ i ∈ Γ) →
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ G.dimension ∧
      ∃ relations : Finset (Fin m → ℤ), (∀ v ∈ relations, ∀ i, |(v i : ℝ)| ≤ R) ∧
        let A := (Submodule.span ℤ
          (integerCombination γ '' (relations : Set (Fin m → ℤ)))).toAddSubgroup
        ((((fun g => _root_.PhilipponMultiplicity.translate g (A : Set G.Point)) '' samplingGrid γ R).ncard : ℝ) ≤
          ((D : ℝ) / c) ^ r) ∧
        ∃ Q : Finset G.CoordinateRing,
          (∀ F ∈ Q, ∃ d : G.FactorIndex → ℕ,
            G.ambient.IsHomogeneous F d ∧
              ∀ i, (d i : ℝ) ≤ (a : ℝ) ^ G.dimension * (D : ℝ)) ∧
          (∀ x ∈ A, ∀ F ∈ Q, G.ambient.eval F (G.embedding x) = 0) ∧
          ∀ q ∈ (G.vanishingIdeal Set.univ ⊔ Ideal.span (Q : Set G.CoordinateRing)).minimalPrimes,
            (∃ x ∈ Γ, x ∈ idealZeroLocusOnGroup G q) →
            varietyDimension G (idealZeroLocusOnGroup G q) ≤ G.dimension - r := by
  exact local_prime_estimate_of_pointed_prime_orbit
    (@masser_wustholz_pointed_prime_orbit) K hK E hn hconnected a b ha hb
    htranslation hclosure m D hm hD γ R hR P hP
