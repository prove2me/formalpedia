-- Prove2me | solution 1 for PI.VolStabW.exists_coord_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:01:48.896321+00:00
-- url     : https://prove2.me/submissions/78938921-e2fd-453d-8e02-f958f4ce1969

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfSS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfTR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open scoped TensorProduct
open PI.AdicCompletionValuation
namespace PI.VolStabW
theorem _root_.solution {X : Type} [AddCommGroup X] [TopologicalSpace X] {N : ℕ}
    (e : X ≃ₜ (Fin N → ℝ)) (he : ∀ x y, e (x + y) = e x + e y) (H : AddSubgroup X)
    (hH : IsClosed (H : Set X)) (hdiv : ∀ n : ℕ, 0 < n → ∀ x ∈ H, ∃ y ∈ H, n • y = x) :
    ∃ (m : ℕ) (eH : H ≃ₜ (Fin m → ℝ)), ∀ x y, eH (x + y) = eH x + eH y := by
  let eA : X →+ (Fin N → ℝ) := AddMonoidHom.mk' e he
  have hq : ∀ (q : ℚ), ∀ x ∈ H, (q : ℝ) • e x ∈ e '' (H : Set X) := by
    intro q x hx
    obtain ⟨y, hy, hyx⟩ := hdiv q.den q.den_pos x hx
    refine ⟨q.num • y, H.zsmul_mem hy _, ?_⟩
    have e1 : e (q.num • y) = (q.num : ℝ) • e y := by
      rw [show e (q.num • y) = eA (q.num • y) from rfl, map_zsmul, Int.cast_smul_eq_zsmul]; rfl
    have e2 : e x = (q.den : ℝ) • e y := by
      rw [← hyx, show e (q.den • y) = eA (q.den • y) from rfl, map_nsmul, Nat.cast_smul_eq_nsmul]
      rfl
    rw [e1, e2, smul_smul]
    congr 1
    exact_mod_cast (Rat.mul_den_eq_num q).symm
  have hcl : IsClosed (e '' (H : Set X)) := e.isClosedMap _ hH
  let W : Submodule ℝ (Fin N → ℝ) :=
    { carrier := e '' (H : Set X)
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, H.add_mem hx hy, he x y⟩
      zero_mem' := ⟨0, H.zero_mem, map_zero eA⟩
      smul_mem' := by
        rintro r _ ⟨x, hx, rfl⟩
        have hc : IsClosed {s : ℝ | s • e x ∈ e '' (H : Set X)} :=
          hcl.preimage (continuous_id.smul continuous_const)
        have hsub : Set.range ((↑) : ℚ → ℝ) ⊆ {s : ℝ | s • e x ∈ e '' (H : Set X)} := by
          rintro _ ⟨q, rfl⟩; exact hq q x hx
        have := (hc.closure_subset_iff.2 hsub) (Rat.denseRange_cast (𝕜 := ℝ) r)
        exact this }
  let e0 : H ≃ₜ W := e.subtype (p := fun x => x ∈ H) (q := fun y => y ∈ W) (fun x => by
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨x', hx', hx'e⟩; rw [← e.injective hx'e]; exact hx')
  let L := ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := W)
    (F := Fin (Module.finrank ℝ W) → ℝ) (Module.finrank_fin_fun ℝ).symm
  refine ⟨_, e0.trans L.toHomeomorph, fun x y => ?_⟩
  show L (e0 (x + y)) = L (e0 x) + L (e0 y)
  rw [show e0 (x + y) = e0 x + e0 y from Subtype.ext (he x y), map_add]
end PI.VolStabW
