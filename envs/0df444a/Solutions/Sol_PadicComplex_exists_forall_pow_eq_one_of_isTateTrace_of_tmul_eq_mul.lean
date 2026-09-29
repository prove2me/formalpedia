-- Prove2me | solution 1 for PadicComplex.exists_forall_pow_eq_one_of_isTateTrace_of_tmul_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/8134c3b8-7265-52c2-a9dd-2262256c8f19

import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PadicComplex_TateTrace
import Theorems.Thm_PadicComplex_forall_smul_eq_self_iff_mem_closure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicComplex_exists_forall_pow_eq_one_of_isTateTrace_of_tmul_eq_mul

set_option autoImplicit false

noncomputable section

namespace TSV

open scoped TensorProduct Matrix
open UniformSpace

variable {p : ℕ} [Fact p.Prime]

local notation "Ω" => PadicAlgCl p
local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

section coords

variable (p)
variable {L : Type*} [Field L] [Algebra ℚ_[p] L] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι ℚ_[p] L)

def coord (z : ℂ_[p] ⊗[ℚ_[p]] L) (i : ι) : ℂ_[p] :=
  (Algebra.TensorProduct.basis ℂ_[p] b).repr z i

omit [Fintype ι] [DecidableEq ι] in
@[scoped simp] lemma coord_zero (i : ι) : coord p b 0 i = 0 := by simp [coord]

omit [Fintype ι] [DecidableEq ι] in
@[scoped simp] lemma coord_add (z w : ℂ_[p] ⊗[ℚ_[p]] L) (i : ι) :
    coord p b (z + w) i = coord p b z i + coord p b w i := by
  simp [coord]

omit [Fintype ι] [DecidableEq ι] in
@[scoped simp] lemma coord_tmul (a : ℂ_[p]) (l : L) (i : ι) :
    coord p b (a ⊗ₜ[ℚ_[p]] l) i = a * algebraMap ℚ_[p] ℂ_[p] (b.repr l i) := by
  simp [coord, Algebra.TensorProduct.basis_repr_tmul, Finsupp.mapRange_apply]

omit [Fintype ι] [DecidableEq ι] in

lemma coord_map_gal (σ : Γ) (z : ℂ_[p] ⊗[ℚ_[p]] L) (i : ι) :
    coord p b (Algebra.TensorProduct.map (PadicComplex.galAlgHom p σ) (AlgHom.id ℚ_[p] L) z) i =
      σ • coord p b z i := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a l =>
      rw [Algebra.TensorProduct.map_tmul, coord_tmul, AlgHom.id_apply,
        PadicComplex.galAlgHom_apply, coord_tmul, smul_mul', PadicComplex.smul_algebraMap]
  | add z w hz hw =>
      rw [map_add, coord_add, coord_add, hz, hw, smul_add]

lemma coord_one_tmul_mul (ℓ : L) (z : ℂ_[p] ⊗[ℚ_[p]] L) (i : ι) :
    coord p b (((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ℓ) * z) i =
      ∑ j, algebraMap ℚ_[p] ℂ_[p] (Algebra.leftMulMatrix b ℓ i j) * coord p b z j := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, coord_tmul]
      have h := congrFun (Algebra.leftMulMatrix_mulVec_repr b ℓ m) i
      simp only [Matrix.mulVec, dotProduct] at h
      rw [← h, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [coord_tmul, map_mul]
      ring
  | add z w hz hw =>
      rw [mul_add, coord_add, hz, hw, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [coord_add, mul_add]

omit [Fintype ι] [DecidableEq ι] in
lemma exists_coord_ne_zero {z : ℂ_[p] ⊗[ℚ_[p]] L} (hz : z ≠ 0) : ∃ i, coord p b z i ≠ 0 := by
  by_contra h
  push Not at h
  apply hz
  have : (Algebra.TensorProduct.basis ℂ_[p] b).repr z = 0 := by
    ext i
    exact h i
  simpa using this

end coords

lemma exists_pow_mem_fixingSubgroup (M : IntermediateField ℚ_[p] Ω) [FiniteDimensional ℚ_[p] M] :
    ∃ N : ℕ, 0 < N ∧ ∀ σ : Γ, σ ^ N ∈ M.fixingSubgroup := by
  classical
  set c := Fintype.card (M →ₐ[ℚ_[p]] Ω) with hc
  refine ⟨c.factorial, Nat.factorial_pos c, fun σ => ?_⟩
  let f : Fin (c + 1) → (M →ₐ[ℚ_[p]] Ω) := fun n =>
    ((σ ^ (n : ℕ) : Γ) : Ω →ₐ[ℚ_[p]] Ω).comp M.val
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f
    (by simp only [Fintype.card_fin]; omega)
  have key : ∀ i j : Fin (c + 1), i < j → f i = f j → σ ^ c.factorial ∈ M.fixingSubgroup := by
    intro i j hlt hf
    have hk : σ ^ ((j : ℕ) - i) ∈ M.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have h1 := congrArg (fun g : M →ₐ[ℚ_[p]] Ω => g ⟨y, hy⟩) hf
      simp only [f, AlgHom.comp_apply, IntermediateField.val_mk, AlgEquiv.coe_algHom] at h1
      have hj : (j : ℕ) = (i : ℕ) + ((j : ℕ) - i) := by omega
      rw [hj, pow_add, AlgEquiv.mul_apply] at h1
      exact ((σ ^ (i : ℕ)).injective h1).symm
    have hdvd : ((j : ℕ) - i) ∣ c.factorial :=
      Nat.dvd_factorial (by omega) (by have := j.2; omega)
    obtain ⟨q, hq⟩ := hdvd
    rw [hq, pow_mul]
    exact Subgroup.pow_mem _ hk q
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hfij
  · exact key j i h hfij.symm

section tower

variable (p)
variable (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) (hmono : Monotone Km)

include hmono

def towerSubmodule : Submodule ℚ_[p] ℂ_[p] where
  carrier := ⋃ m : ℕ, Set.range fun k : Km m => ((k : Ω) : ℂ_[p])
  zero_mem' := Set.mem_iUnion.mpr ⟨0, ⟨0, by simp⟩⟩
  add_mem' := by
    intro u v hu hv
    obtain ⟨m, ⟨k, rfl⟩⟩ := Set.mem_iUnion.mp hu
    obtain ⟨n, ⟨l, rfl⟩⟩ := Set.mem_iUnion.mp hv
    refine Set.mem_iUnion.mpr ⟨max m n, ⟨⟨(k : Ω) + l, ?_⟩, ?_⟩⟩
    · exact add_mem (hmono (le_max_left m n) k.2) (hmono (le_max_right m n) l.2)
    · simp [Completion.coe_add]
  smul_mem' := by
    intro a u hu
    obtain ⟨m, ⟨k, rfl⟩⟩ := Set.mem_iUnion.mp hu
    refine Set.mem_iUnion.mpr ⟨m, ⟨⟨algebraMap ℚ_[p] Ω a * (k : Ω), ?_⟩, ?_⟩⟩
    · exact mul_mem (algebraMap_mem (Km m) a) k.2
    · simp only
      rw [Completion.coe_mul, Algebra.smul_def, IsScalarTower.algebraMap_apply ℚ_[p] Ω ℂ_[p]]
      rfl

lemma coe_towerSubmodule_topologicalClosure :
    ((towerSubmodule p Km hmono).topologicalClosure : Set ℂ_[p]) =
      PadicComplex.towerClosure p Km := by
  rw [Submodule.topologicalClosure_coe]
  rfl

lemma mem_towerClosure_iff (z : ℂ_[p]) :
    z ∈ PadicComplex.towerClosure p Km ↔ z ∈ (towerSubmodule p Km hmono).topologicalClosure := by
  rw [← SetLike.mem_coe, coe_towerSubmodule_topologicalClosure]

lemma add_mem_towerClosure {z w : ℂ_[p]} (hz : z ∈ PadicComplex.towerClosure p Km)
    (hw : w ∈ PadicComplex.towerClosure p Km) : z + w ∈ PadicComplex.towerClosure p Km := by
  rw [mem_towerClosure_iff p Km hmono] at hz hw ⊢
  exact add_mem hz hw

lemma algebraMap_mul_mem_towerClosure (a : ℚ_[p]) {z : ℂ_[p]}
    (hz : z ∈ PadicComplex.towerClosure p Km) :
    algebraMap ℚ_[p] ℂ_[p] a * z ∈ PadicComplex.towerClosure p Km := by
  rw [mem_towerClosure_iff p Km hmono] at hz ⊢
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ a hz

lemma sum_mem_towerClosure {ι : Type*} (s : Finset ι) (g : ι → ℂ_[p])
    (hg : ∀ i ∈ s, g i ∈ PadicComplex.towerClosure p Km) :
    ∑ i ∈ s, g i ∈ PadicComplex.towerClosure p Km := by
  rw [mem_towerClosure_iff p Km hmono]
  exact Submodule.sum_mem _ fun i hi => (mem_towerClosure_iff p Km hmono _).mp (hg i hi)

end tower

private lemma _root_.PadicComplex.IsTateTrace.map_algebraMap_mul
    {Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)} {m : ℕ} {d : ℝ} {R : ℂ_[p] → ℂ_[p]}
    (hR : PadicComplex.IsTateTrace p Km m d R) (a : ℚ_[p]) {z : ℂ_[p]}
    (hz : z ∈ PadicComplex.towerClosure p Km) :
    R (algebraMap ℚ_[p] ℂ_[p] a * z) = algebraMap ℚ_[p] ℂ_[p] a * R z := by
  have h := hR.map_mul_left (algebraMap ℚ_[p] (Km m) a) z hz
  have hcoe : (((algebraMap ℚ_[p] (Km m) a : Km m) : Ω) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] a := by
    rw [IsScalarTower.algebraMap_apply ℚ_[p] Ω ℂ_[p]]
    rfl
  rwa [hcoe] at h

p2m_alias "P2MW.S_PadicComplex_exists_forall_pow_eq_one_of_isTateTrace_of_tmul_eq_mul.PadicComplex.IsTateTrace.map_algebraMap_mul" "PadicComplex.IsTateTrace.map_algebraMap_mul"

private lemma _root_.PadicComplex.IsTateTrace.map_sum_algebraMap_mul
    {Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)} (hmono : Monotone Km)
    {m : ℕ} {d : ℝ} {R : ℂ_[p] → ℂ_[p]}
    (hR : PadicComplex.IsTateTrace p Km m d R) {ι : Type*} (s : Finset ι) (a : ι → ℚ_[p])
    (g : ι → ℂ_[p]) (hg : ∀ i ∈ s, g i ∈ PadicComplex.towerClosure p Km) :
    R (∑ i ∈ s, algebraMap ℚ_[p] ℂ_[p] (a i) * g i) =
      ∑ i ∈ s, algebraMap ℚ_[p] ℂ_[p] (a i) * R (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      have h0 := hR.apply_coe 0
      simpa using h0
  | insert j s hj ih =>
      have hg' : ∀ i ∈ s, g i ∈ PadicComplex.towerClosure p Km :=
        fun i hi => hg i (Finset.mem_insert_of_mem hi)
      have hgj : g j ∈ PadicComplex.towerClosure p Km := hg j (Finset.mem_insert_self j s)
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        hR.map_add _ (algebraMap_mul_mem_towerClosure p Km hmono _ hgj)
          _ (sum_mem_towerClosure p Km hmono s _
              (fun i hi => algebraMap_mul_mem_towerClosure p Km hmono _ (hg' i hi))),
        ih hg', hR.map_algebraMap_mul (a j) hgj]

p2m_alias "P2MW.S_PadicComplex_exists_forall_pow_eq_one_of_isTateTrace_of_tmul_eq_mul.PadicComplex.IsTateTrace.map_sum_algebraMap_mul" "PadicComplex.IsTateTrace.map_sum_algebraMap_mul"

section main

variable (p)
variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))
  (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) (hmono : Monotone Km)
  (hK : ∀ m, K ≤ Km m)
  {L : Type*} [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
  (ψ : K.fixingSubgroup →* Lˣ)
  (hψ' : ∀ σ : K.fixingSubgroup,
    (∀ m, (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ∈ (Km m).fixingSubgroup) → ψ σ = 1)
  (x : ℂ_[p] ⊗[ℚ_[p]] L)
  (hψ : ∀ σ : K.fixingSubgroup,
    Algebra.TensorProduct.map
        (PadicComplex.galAlgHom p (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (AlgHom.id ℚ_[p] L)
        x =
      ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ((ψ σ : Lˣ) : L)) * x)

include hmono hK hψ' hψ

omit [FiniteDimensional ℚ_[p] L] in

lemma coord_mem_towerClosure {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ_[p] L)
    (i : ι) : coord p b x i ∈ PadicComplex.towerClosure p Km := by
  set Kinf : IntermediateField ℚ_[p] Ω := ⨆ m, Km m with hKinf
  have hfix : ∀ σ : Γ, σ ∈ Kinf.fixingSubgroup → σ • coord p b x i = coord p b x i := by
    intro σ hσ
    have hσK : σ ∈ K.fixingSubgroup :=
      IntermediateField.fixingSubgroup_le ((hK 0).trans (le_iSup Km 0)) hσ
    have hσm : ∀ m, σ ∈ (Km m).fixingSubgroup := fun m =>
      IntermediateField.fixingSubgroup_le (le_iSup Km m) hσ
    have h1 : ψ ⟨σ, hσK⟩ = 1 := hψ' ⟨σ, hσK⟩ hσm
    have h2 := hψ ⟨σ, hσK⟩
    rw [h1, Units.val_one, ← Algebra.TensorProduct.one_def, one_mul] at h2
    have h3 : coord p b (Algebra.TensorProduct.map (PadicComplex.galAlgHom p σ)
        (AlgHom.id ℚ_[p] L) x) i = coord p b x i := congrArg (coord p b · i) h2
    rwa [coord_map_gal] at h3
  have hmem :=
    (PadicComplex.forall_smul_eq_self_iff_mem_closure p Kinf (coord p b x i)).mp hfix
  have hset : (Set.range fun k : Kinf => ((k : Ω) : ℂ_[p])) =
      ⋃ m, Set.range fun k : Km m => ((k : Ω) : ℂ_[p]) := by
    ext z
    constructor
    · rintro ⟨k, rfl⟩
      have hk : (k : Ω) ∈ ((⨆ m, Km m : IntermediateField ℚ_[p] Ω) : Set Ω) := k.2
      rw [IntermediateField.coe_iSup_of_directed hmono.directed_le] at hk
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hk
      exact Set.mem_iUnion.mpr ⟨m, ⟨⟨(k : Ω), hm⟩, rfl⟩⟩
    · intro hz
      obtain ⟨m, ⟨k, rfl⟩⟩ := Set.mem_iUnion.mp hz
      exact ⟨⟨(k : Ω), (le_iSup Km m) k.2⟩, rfl⟩
  rw [hset] at hmem
  exact hmem

omit [FiniteDimensional ℚ_[p] L] in

lemma apply_eq_one_of_generator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ_[p] L) (i₁ : ι)
    {m₁ : ℕ} (k₁ : Km m₁) {ε : ℝ}
    (hk₁ : ‖coord p b x i₁ - ((k₁ : Ω) : ℂ_[p])‖ < ε)
    {d : ℝ} (hε : (|d| + 1) * ε ≤ ‖coord p b x i₁‖)
    {m : ℕ} (hm : m₁ ≤ m) {R : ℂ_[p] → ℂ_[p]} (hR : PadicComplex.IsTateTrace p Km m d R)
    (σ : Γ) (hσ : σ ∈ (Km m).fixingSubgroup) (hσ' : σ ∉ (Km (m + 1)).fixingSubgroup) :
    ψ ⟨σ, IntermediateField.fixingSubgroup_le (hK m) hσ⟩ = 1 := by
  have hσK : σ ∈ K.fixingSubgroup := IntermediateField.fixingSubgroup_le (hK m) hσ
  by_contra hne
  set ℓ : L := ((ψ ⟨σ, hσK⟩ : Lˣ) : L) with hℓ
  have hℓ1 : ℓ - 1 ≠ 0 := by
    intro h
    apply hne
    rw [sub_eq_zero] at h
    exact Units.ext h

  set c : ι → ℂ_[p] := fun i => coord p b x i with hc
  have hcX : ∀ i, c i ∈ PadicComplex.towerClosure p Km := fun i =>
    coord_mem_towerClosure p K Km hmono hK ψ hψ' x hψ b i
  set A : Matrix ι ι ℚ_[p] := Algebra.leftMulMatrix b ℓ with hA

  have hE1 : ∀ i, σ • c i = ∑ j, algebraMap ℚ_[p] ℂ_[p] (A i j) * c j := by
    intro i
    have h := congrArg (fun z => coord p b z i) (hψ ⟨σ, hσK⟩)
    simp only [coord_map_gal, coord_one_tmul_mul] at h
    exact h

  have hE2 : ∀ i, R (c i) = ∑ j, algebraMap ℚ_[p] ℂ_[p] (A i j) * R (c j) := by
    intro i
    have h1 : R (σ • c i) = R (c i) := hR.apply_smul σ hσ (c i) (hcX i)
    rw [← h1, hE1 i]
    exact hR.map_sum_algebraMap_mul hmono Finset.univ (fun j => A i j) c (fun j _ => hcX j)

  have hRc : ∀ j, R (c j) = 0 := by
    set A' : Matrix ι ι ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).mapMatrix (A - 1) with hA'
    have hunit : IsUnit A' := by
      have h1 : IsUnit (ℓ - 1) := isUnit_iff_ne_zero.mpr hℓ1
      have h2 : IsUnit (A - 1) := by
        have : A - 1 = Algebra.leftMulMatrix b (ℓ - 1) := by
          rw [map_sub, map_one]
        rw [this]
        exact h1.map _
      exact h2.map _
    have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hunit
    set v : ι → ℂ_[p] := fun j => R (c j) with hv
    have hv0 : A' *ᵥ v = A' *ᵥ 0 := by
      rw [Matrix.mulVec_zero]
      ext i
      rw [hA', map_sub, map_one, Matrix.sub_mulVec, Pi.sub_apply, Matrix.one_mulVec,
        Pi.zero_apply, sub_eq_zero, RingHom.mapMatrix_apply, Matrix.mulVec, dotProduct]
      simp only [Matrix.map_apply]
      exact (hE2 i).symm
    have := hinj hv0
    intro j
    exact congrFun this j

  have hest := hR.norm_sub_apply_le σ hσ hσ' (c i₁) (hcX i₁)
  rw [hRc i₁, sub_zero] at hest

  have hk₁m : (k₁ : Ω) ∈ Km m := hmono hm k₁.2
  have hσk : σ • ((k₁ : Ω) : ℂ_[p]) = ((k₁ : Ω) : ℂ_[p]) := by
    rw [PadicComplex.smul_coe]
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    rw [hσ _ hk₁m]
  have hmove : ‖σ • c i₁ - c i₁‖ ≤ ‖c i₁ - ((k₁ : Ω) : ℂ_[p])‖ := by
    have hrw : σ • c i₁ - c i₁ =
        σ • (c i₁ - ((k₁ : Ω) : ℂ_[p])) + (-(c i₁ - ((k₁ : Ω) : ℂ_[p]))) := by
      rw [smul_sub, hσk]
      abel
    rw [hrw]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [PadicComplex.norm_smul_eq, norm_neg, max_self]

  have hpos : 0 < ‖c i₁‖ := by
    have h0 : (0 : ℝ) ≤ (|d| + 1) * ε := by
      have : 0 ≤ ‖coord p b x i₁ - ((k₁ : Ω) : ℂ_[p])‖ := norm_nonneg _
      nlinarith [abs_nonneg d]
    have h1 : 0 < ε := lt_of_le_of_lt (norm_nonneg _) hk₁
    rcases eq_or_lt_of_le (norm_nonneg (c i₁)) with h | h
    · exfalso
      have : (|d| + 1) * ε ≤ 0 := by rw [h]; exact hε
      nlinarith [abs_nonneg d]
    · exact h
  have hchain : ‖c i₁‖ < ‖c i₁‖ := by
    calc ‖c i₁‖ ≤ d * ‖σ • c i₁ - c i₁‖ := hest
      _ ≤ |d| * ‖σ • c i₁ - c i₁‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self d) (norm_nonneg _)
      _ ≤ |d| * ‖c i₁ - ((k₁ : Ω) : ℂ_[p])‖ :=
          mul_le_mul_of_nonneg_left hmove (abs_nonneg d)
      _ < (|d| + 1) * ε := by
          have h1 : |d| * ‖c i₁ - ((k₁ : Ω) : ℂ_[p])‖ ≤ |d| * ε :=
            mul_le_mul_of_nonneg_left hk₁.le (abs_nonneg d)
          have h2 : 0 < ε := lt_of_le_of_lt (norm_nonneg _) hk₁
          nlinarith
      _ ≤ ‖c i₁‖ := hε
  exact lt_irrefl _ hchain

lemma exists_level_trivial (hx : x ≠ 0)
    (d : ℝ) (m₀ : ℕ)
    (hR : ∀ m, m₀ ≤ m → ∃ R : ℂ_[p] → ℂ_[p], PadicComplex.IsTateTrace p Km m d R) :
    ∃ M : ℕ, ∀ σ : K.fixingSubgroup, (σ : Γ) ∈ (Km M).fixingSubgroup → ψ σ = 1 := by
  classical
  by_cases hstab : ∃ M, ∀ m, M ≤ m → (Km m).fixingSubgroup ≤ (Km (m + 1)).fixingSubgroup
  ·
    obtain ⟨M, hM⟩ := hstab
    refine ⟨M, fun σ hσ => hψ' σ (fun m => ?_)⟩
    rcases le_total m M with hm | hm
    · exact IntermediateField.fixingSubgroup_le (hmono hm) hσ
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
      clear hm
      induction k with
      | zero => rw [Nat.add_zero]; exact hσ
      | succ k ih =>
          have := hM (M + k) (Nat.le_add_right M k) ih
          rw [← Nat.add_assoc]
          exact this
  · push Not at hstab

    set b := Module.finBasis ℚ_[p] L with hb
    obtain ⟨i₁, hi₁⟩ := exists_coord_ne_zero p b hx
    have hpos : 0 < ‖coord p b x i₁‖ := norm_pos_iff.mpr hi₁
    set ε : ℝ := ‖coord p b x i₁‖ / (|d| + 1) with hεdef
    have hd1 : 0 < |d| + 1 := by positivity
    have hε : 0 < ε := div_pos hpos hd1
    have hεle : (|d| + 1) * ε ≤ ‖coord p b x i₁‖ := by
      rw [hεdef, mul_div_cancel₀ _ hd1.ne']
    have hcX : coord p b x i₁ ∈ PadicComplex.towerClosure p Km :=
      coord_mem_towerClosure p K Km hmono hK ψ hψ' x hψ b i₁
    obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hcX ε hε
    obtain ⟨m₁, ⟨k₁, rfl⟩⟩ := Set.mem_iUnion.mp hy
    rw [dist_eq_norm] at hdist

    obtain ⟨m, hm, hgen⟩ := hstab (max m₀ m₁)
    obtain ⟨σ₀, hσ₀, hσ₀'⟩ := Set.not_subset.mp hgen
    obtain ⟨R, hR⟩ := hR m ((le_max_left m₀ m₁).trans hm)
    have hm₁ : m₁ ≤ m := (le_max_right m₀ m₁).trans hm

    have hkill : ∀ σ : Γ, ∀ hσ : σ ∈ (Km m).fixingSubgroup, σ ∉ (Km (m + 1)).fixingSubgroup →
        ψ ⟨σ, IntermediateField.fixingSubgroup_le (hK m) hσ⟩ = 1 :=
      fun σ hσ hσ' => apply_eq_one_of_generator p K Km hmono hK ψ hψ' x hψ b i₁ k₁ hdist hεle
        hm₁ hR σ hσ hσ'

    refine ⟨m, fun τ hτ => ?_⟩
    by_cases hτ' : (τ : Γ) ∈ (Km (m + 1)).fixingSubgroup
    · have hσ₀K : σ₀ ∈ K.fixingSubgroup := IntermediateField.fixingSubgroup_le (hK m) hσ₀
      set ρ : Γ := (τ : Γ) * σ₀⁻¹ with hρ
      have hρm : ρ ∈ (Km m).fixingSubgroup := mul_mem hτ (inv_mem hσ₀)
      have hρ' : ρ ∉ (Km (m + 1)).fixingSubgroup := by
        intro h
        apply hσ₀'
        have : σ₀ = ρ⁻¹ * (τ : Γ) := by rw [hρ]; group
        rw [this]
        exact mul_mem (inv_mem h) hτ'
      have h1 := hkill ρ hρm hρ'
      have h2 := hkill σ₀ hσ₀ hσ₀'
      have hτeq : τ = ⟨ρ, IntermediateField.fixingSubgroup_le (hK m) hρm⟩ *
          ⟨σ₀, IntermediateField.fixingSubgroup_le (hK m) hσ₀⟩ := by
        apply Subtype.ext
        show (τ : Γ) = ρ * σ₀
        rw [hρ]; group
      rw [hτeq, map_mul, h1, h2, one_mul]
    · have := hkill (τ : Γ) hτ hτ'
      simpa using this

theorem main (hfin : ∀ m, FiniteDimensional ℚ_[p] (Km m)) (hx : x ≠ 0)
    (d : ℝ) (m₀ : ℕ)
    (hR : ∀ m, m₀ ≤ m → ∃ R : ℂ_[p] → ℂ_[p], PadicComplex.IsTateTrace p Km m d R) :
    ∃ n : ℕ, 0 < n ∧ ∀ σ : K.fixingSubgroup, ψ σ ^ n = 1 := by
  obtain ⟨M, hM⟩ := exists_level_trivial p K Km hmono hK ψ hψ' x hψ hx d m₀ hR
  haveI := hfin M
  obtain ⟨N, hN, hpow⟩ := exists_pow_mem_fixingSubgroup (p := p) (Km M)
  refine ⟨N, hN, fun σ => ?_⟩
  rw [← map_pow]
  apply hM
  simpa using hpow σ

end main

end TSV
p2m_reactivate "P2MW.S_PadicComplex_exists_forall_pow_eq_one_of_isTateTrace_of_tmul_eq_mul.TSV"

end
p2m_reactivate "P2MW.S_PadicComplex_exists_forall_pow_eq_one_of_isTateTrace_of_tmul_eq_mul.TSV"

open scoped TensorProduct in
theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) (hmono : Monotone Km)
    (hK : ∀ m, K ≤ Km m) (hfin : ∀ m, FiniteDimensional ℚ_[p] (Km m))
    (d : ℝ) (m₀ : ℕ)
    (hR : ∀ m, m₀ ≤ m → ∃ R : ℂ_[p] → ℂ_[p], PadicComplex.IsTateTrace p Km m d R)
    (L : Type*) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    (ψ : K.fixingSubgroup →* Lˣ)
    (hψ' : ∀ σ : K.fixingSubgroup,
      (∀ m, (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) ∈ (Km m).fixingSubgroup) → ψ σ = 1)
    (x : ℂ_[p] ⊗[ℚ_[p]] L) (hx : x ≠ 0)
    (hψ : ∀ σ : K.fixingSubgroup,
      Algebra.TensorProduct.map
          (PadicComplex.galAlgHom p (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) (AlgHom.id ℚ_[p] L)
          x =
        ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ((ψ σ : Lˣ) : L)) * x) :
    ∃ n : ℕ, 0 < n ∧ ∀ σ : K.fixingSubgroup, ψ σ ^ n = 1 :=
  TSV.main p K Km hmono hK ψ hψ' x hψ hfin hx d m₀ hR

end S_PadicComplex_exists_forall_pow_eq_one_of_isTateTrace_of_tmul_eq_mul
end P2MW
export P2MW.S_PadicComplex_exists_forall_pow_eq_one_of_isTateTrace_of_tmul_eq_mul (solution)
