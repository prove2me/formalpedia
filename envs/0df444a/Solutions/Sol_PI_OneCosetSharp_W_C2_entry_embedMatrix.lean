-- Prove2me | solution 1 for PI.OneCosetSharp.W.C2.entry_embedMatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:51:36.216795+00:00
-- url     : https://prove2.me/submissions/7d108bd9-f6a8-4260-9161-a4c076d548eb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_EntryEmbedMatrix
import Theorems.Thm_P2M_PI_OneCosetSharp_W_C2_toLin__eN_a4eb870cf892
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.OneCosetSharp.W.C2
open Loc LocE
variable {k : Type} [Field k]
private theorem atN_of_lt' {N : ℕ} (v : Fin N → k) {i : ℕ} (h : i < N) : PI.OneCosetSharp.Loc.atN v i = v ⟨i, h⟩ := by
  unfold PI.OneCosetSharp.Loc.atN
  simp [h]
end PI.OneCosetSharp.W.C2
end
end

set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W PI.OneCosetSharp.W.C2
open Loc LocE
variable {k : Type} [Field k]
namespace PI.OneCosetSharp.W.C2
theorem _root_.solution {n' c n : ℕ} (k₀ : ℕ) (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (τ : FC n' (c + 1) n c → k)
    (p p' : ℕ) (hp : fIdx k₀ c n p < n + c) (hp' : fIdx k₀ (c + 1) n' p' < n' + (c + 1)) :
    ent k₀ (c + 1) n' c n (xx1 xj τ) p p' =
      (if hf : IsFree n' n c (fIdx k₀ c n p) (fIdx k₀ (c + 1) n' p') then τ ⟨(⟨_, hp⟩, ⟨_, hp'⟩), hf⟩
       else if hs : fIdx k₀ (c + 1) n' p' < n' then
          (if hl : fIdx k₀ c n p < n then LinearMap.toMatrix' xj ⟨_, hl⟩ ⟨_, hs⟩ else 0)
       else if fIdx k₀ c n p = n + (fIdx k₀ (c + 1) n' p' - n') then 1 else 0) := by
  unfold PI.OneCosetSharp.ent PI.OneCosetSharp.Loc.xx1
  rw [toLin'_eN _ _ hp', atN_of_lt' _ hp]
  rfl
end PI.OneCosetSharp.W.C2
