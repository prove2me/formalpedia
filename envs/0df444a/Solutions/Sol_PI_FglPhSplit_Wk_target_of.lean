-- Prove2me | solution 1 for PI.FglPhSplit.Wk.target_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:46:31.958462+00:00
-- url     : https://prove2.me/submissions/df759f35-d3ef-4f55-b672-379e5b7a9d13

import Definitions.Def_Formalism_PeriodIntegrals_FglPhSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_Development
import Theorems.Thm_PI_FglPhSplit_Wk_simeqW_refl
import Theorems.Thm_PI_FglPhSplit_Wk_simeqW_of_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglPhSplit PI.FglPhSplit.Wk
open PI.FglPhSplit MvPowerSeries
namespace PI.FglPhSplit.Wk
theorem _root_.solution (h2 : S2) (h3 : S3) (h4 : S4) : Target := by
  intro K _ _ W g S hex hl hph hSD hDI κ ι ι' _ _ _ b b' b'' hb hb' hb'' hD hbb hb'b
  have hmem : ∀ e k, Sum.elim b b' e k ∈ S := by
    rintro (e | e) k
    · exact hb e k
    · exact hb' e k
  have hA := hSD κ (ι ⊕ ι) ι' (Sum.elim b b') b'' hmem hb''
  have hR0 : g.sdR (Sum.elim b b') b'' = 0 := by
    apply h2 K g hex hl hph κ (ι ⊕ ι) ι' (Sum.elim b b') b''
    rintro (e | e) f
    · exact hbb e f
    · exact hb'b e f
  have hB := h4 K W g hex hl κ ι ι' b b' (hDI κ ι b b' hb hb' hD)
  have hC := h3 K W _ _ _ _ _ hA hB
  have hE := h3 K W _ _ _ _ _ hC
    (simeqW_refl W (g.PhV b'' (fun f => (X (Sum.inr f) : MvPowerSeries ((ι ⊕ ι) ⊕ ι') K))))
  refine simeqW_of_eq hE ?_ ?_
  · unfold Dat.sdL
    abel
  · rw [hR0, zero_add]
end PI.FglPhSplit.Wk
