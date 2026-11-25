-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_embedH_injective_3c4c852e48a6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:15:13.42322+00:00
-- url     : https://prove2.me/submissions/b86a8862-99a4-460f-8d10-7a9b8b23a281

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechTransport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_embedC_injective_bbfdf92a6e8b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_exists_embedC_eq_d6410787624d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable (M : FinGradedSub (S := S) (x := x) Ω) (c : ℤ)
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace FinGradedSub
theorem _root_.solution (n : ℕ) : Function.Injective (M.embedH c n) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change Submodule.Quotient.mk _ = 0 at hy
  have hz := (Submodule.Quotient.mk_eq_zero _).mp hy
  refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
  cases n with
  | zero =>
    change M.embedC c 0 (z : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) 0) ∈
      (⊥ : Submodule S _) at hz
    change (z : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) 0) ∈ (⊥ : Submodule S _)
    rw [Submodule.mem_bot] at hz ⊢
    exact M.embedC_injective c 0 (hz.trans (map_zero _).symm)
  | succ n =>
    change M.embedC c (n + 1) (z : Cech.Cochain (fun I : Chart x => (M.tildeSys c).sub I) (n + 1)) ∈
      (Cech.Cdeg (fun _ : StdCell N => ConeLaurent S x) (M.coneDeg c) n).map
        (Cech.d (fun _ : StdCell N => ConeLaurent S x) (supportRes S x) n) at hz
    obtain ⟨w, hw, hwz⟩ := Submodule.mem_map.mp hz
    obtain ⟨t, rfl⟩ := M.exists_embedC_eq c n w hw
    refine LinearMap.mem_range.mpr ⟨t, M.embedC_injective c (n + 1) ?_⟩
    rw [M.embedC_d, hwz]
    rfl
end FinGradedSub
end GroundTheory.Heights₂.Heights.Kleiman
