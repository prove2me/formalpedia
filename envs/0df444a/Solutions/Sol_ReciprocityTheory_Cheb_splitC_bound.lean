-- Prove2me | solution 1 for ReciprocityTheory.Cheb.splitC_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:45:30.586343+00:00
-- url     : https://prove2.me/submissions/e8c3d0ef-9395-4e0f-a412-d1a9fa7f7e4d

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitF
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitC
import Theorems.Thm_ReciprocityTheory_Cheb_splitC_indicator_le
import Theorems.Thm_ReciprocityTheory_Cheb_affine_proper_base_change
import Theorems.Thm_ReciprocityTheory_Cheb_fibre_sum_ge


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (k : ℕ) (S : Set (Prm E)) (hS : S.Finite)
    (h : ∀ q ∉ S, k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard) (s : ℝ) (hs : 1 < s) :
    (k : ℝ) * PE E s ≤ PE E' s + k * hS.toFinset.card := by
  have key := fibre_sum_ge (under (E := E) (E' := E')) (fun P : Prm E' => ((Nrm P : ℕ) : ℝ) ^ (-s))
    (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s)) k (fun P => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (affine_proper_base_change.2.2 E' s hs) (fun q => Real.rpow_nonneg (Nat.cast_nonneg _) _) (affine_proper_base_change.2.2 E s hs) S hS
    (by
      intro q hq
      have hset : {P : Prm E' | under P = q ∧ ((Nrm P : ℕ) : ℝ) ^ (-s) = ((Nrm q : ℕ) : ℝ) ^ (-s)} =
          {P : Prm E' | under P = q ∧ Nrm P = Nrm q} := by
        ext P
        simp only [Set.mem_ofPred_eq]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          have := (Real.rpow_left_inj (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith : -s ≠ 0)).mp h2
          exact_mod_cast this
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by rw [h2]⟩
      rw [hset]
      exact h q hq)
  have hind := splitC_indicator_le S hS s (by linarith)
  unfold PE
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hind hk0]
end ReciprocityTheory.Cheb
