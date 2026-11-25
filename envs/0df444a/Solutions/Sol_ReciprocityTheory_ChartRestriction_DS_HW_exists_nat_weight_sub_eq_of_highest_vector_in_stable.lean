-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.exists_nat_weight_sub_eq_of_highest_vector_in_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:25:21.793657+00:00
-- url     : https://prove2.me/submissions/4a88614e-c50a-44f9-a9d0-23d65e7932ea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_UniqueA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_HighestWeightDifferencesNat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_lie_relation_raise_lower
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_lie_relation_diag_a_lower
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_lie_relation_diag_b_lower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (hF : Formalism.REAL.KRel ε F) {a b : Fin n} (hab : a ≠ b) (he : ε a = ε b)
    (S : Submodule ℂ M) [FiniteDimensional ℂ S] (hS : ∀ y ∈ S, F b a y ∈ S)
    {v : M} (hv : v ∈ S) (hv0 : v ≠ 0) {la lb : ℂ} (ha : F a a v = la • v) (hb : F b b v = lb • v)
    (h0 : F a b v = 0) : ∃ m : ℕ, la - lb = m := by
  classical
  let vk : ℕ → M := fun k => (F b a ^ k) v
  have hvk0 : vk 0 = v := by simp [vk]
  have hvk : ∀ k, vk (k + 1) = F b a (vk k) := fun k => by
    simp only [vk, pow_succ', Module.End.mul_apply]
  have hmem : ∀ k, vk k ∈ S := by
    intro k
    induction k with
    | zero => rw [hvk0]; exact hv
    | succ k ih => rw [hvk]; exact hS _ ih
  have hwa : ∀ k : ℕ, F a a (vk k) = (la - k) • vk k := by
    intro k
    induction k with
    | zero => rw [hvk0, ha]; simp
    | succ k ih =>
      rw [hvk, lie_relation_diag_a_lower hF hab he, ih, map_smul]
      push_cast
      module
  have hwb : ∀ k : ℕ, F b b (vk k) = (lb + k) • vk k := by
    intro k
    induction k with
    | zero => rw [hvk0, hb]; simp
    | succ k ih =>
      rw [hvk, lie_relation_diag_b_lower hF hab he, ih, map_smul]
      push_cast
      module
  have hE : ∀ k : ℕ, F a b (vk (k + 1)) = (((k : ℂ) + 1) * (la - lb - k)) • vk k := by
    intro k
    induction k with
    | zero =>
      rw [hvk, hvk0, lie_relation_raise_lower hF he, h0, map_zero, ha, hb]
      push_cast
      module
    | succ k ih =>
      rw [hvk (k + 1), lie_relation_raise_lower hF he, ih, map_smul, ← hvk, hwa, hwb]
      push_cast
      module
  have hex : ∃ k, vk k = 0 := by
    by_contra hcon
    push_neg at hcon
    have hli : LinearIndependent ℂ vk :=
      Module.End.eigenvectors_linearIndependent' (F a a) (fun k : ℕ => la - k)
        (by
          intro i j hij
          have h1 : (i : ℂ) = j := sub_right_inj.1 hij
          exact_mod_cast h1)
        vk (fun k => Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 (hwa k), hcon k⟩)
    let vs : ℕ → S := fun k => ⟨vk k, hmem k⟩
    have hls : LinearIndependent ℂ vs := LinearIndependent.of_comp S.subtype hli
    exact Module.Finite.not_linearIndependent_of_infinite vs hls
  have hk0 : vk (Nat.find hex) = 0 := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro h
    rw [h, hvk0] at hk0
    exact hv0 hk0
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hvm : vk m ≠ 0 := Nat.find_min hex (by omega)
  have h1 := hE m
  rw [← hm, hk0, map_zero] at h1
  have hcoef : ((m : ℂ) + 1) * (la - lb - m) = 0 := by
    by_contra hne
    exact hvm ((smul_eq_zero.1 h1.symm).resolve_left hne)
  have hm1 : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  refine ⟨m, ?_⟩
  have h2 := (mul_eq_zero.1 hcoef).resolve_left hm1
  linear_combination h2
end ReciprocityTheory.ChartRestriction.DS.HW
