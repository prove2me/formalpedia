-- Prove2me | solution 1 for ThreeSum.TernaryOriginalCollisions.sum_nextCollisions_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:23:27.57983+00:00
-- url     : https://prove2.me/submissions/04cd4a60-0ca5-457e-b380-1883175f182c

import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_admissible_event_bound
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalCollisions
open Finset TernaryOriginalRowMenu
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K E B W : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Field E] [Algebra K E] [Fintype E] [DecidableEq E]
  [Fintype B] [DecidableEq B] [DecidableEq W]
namespace ThreeSum.TernaryOriginalCollisions
theorem _root_.solution {Λ : ℕ} (ℓ : E →ₗ[K] K) (hℓ : ℓ ≠ 0)
    (v : B → Fin Λ → K) (hv : Function.Injective v) (hash : B → W)
    (V : Submodule K (Fin Λ → K)) (hV : V ≠ ⊤) (hp : 3 ≤ Fintype.card K)
    (hsize : 8*Λ*Fintype.card K^2 ≤ Fintype.card E) :
    Fintype.card K * (∑ seed ∈ admissible Λ ℓ V, nextCollisions ℓ v hash seed) ≤
      3*(admissible Λ ℓ V).card*(collisionPairs hash).card := by
  let S := admissible Λ ℓ V
  let C := collisionPairs hash
  have hterm (ab : B × B) (hab : ab ∈ C) :
      Fintype.card K * (S.filter fun seed => row Λ ℓ seed (v ab.1) = row Λ ℓ seed (v ab.2)).card ≤
        3*S.card := by
    have hvne : v ab.1-v ab.2 ≠ 0 := by
      intro hz
      exact (mem_filter.mp hab).2.1 (hv (sub_eq_zero.mp hz))
    have hind : LinearIndependent K (fun _ : Fin 1 => v ab.1-v ab.2) := by
      simpa only [linearIndependent_unique_iff] using hvne
    have hh := admissible_event_bound ℓ hℓ V hV hp
      (fun _ : Fin 1 => v ab.1-v ab.2) hind 0 hsize (by simpa using hsize)
    have he : (S ∩ menuEvent ℓ (fun _ : Fin 1 => v ab.1-v ab.2) 0) =
        S.filter (fun seed => row Λ ℓ seed (v ab.1) = row Λ ℓ seed (v ab.2)) := by
      ext seed
      simp [menuEvent,map_sub,sub_eq_zero,Fin.forall_fin_one]
    simp only [pow_one] at hh
    change Fintype.card K * (S ∩ menuEvent ℓ (fun _ : Fin 1 => v ab.1-v ab.2) 0).card ≤ 3*S.card at hh
    rw [he] at hh
    exact hh
  have hex : (∑ seed ∈ S, nextCollisions ℓ v hash seed) =
      ∑ ab ∈ C, (S.filter fun seed => row Λ ℓ seed (v ab.1) = row Λ ℓ seed (v ab.2)).card := by
    simp only [nextCollisions,card_eq_sum_ones,sum_filter]
    rw [sum_comm]
  rw [hex,mul_sum]
  calc
    _ ≤ ∑ _ab ∈ C, 3*S.card := sum_le_sum hterm
    _ = _ := by simp [S,C,Nat.mul_comm]
end ThreeSum.TernaryOriginalCollisions
