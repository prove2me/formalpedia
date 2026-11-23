-- Prove2me | solution 1 for P2M_Formalism_DworkPowerSeriesWeights_eval__ringHom_eq_ab9ee6c66867
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:32.524801+00:00
-- url     : https://prove2.me/submissions/3fd0839d-c595-4e99-a143-a47250c26cbb

import Definitions.Def_Formalism_GaussJetBounds_StatementM
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {σ A K : Type} [CommRing A] [CommRing K] (ι : MvPolynomial σ A →+* K)
    (P : MvPolynomial σ A) : eval₂ (ι.comp C) (fun i => ι (X i)) P = ι P := by
  have := eval₂_comp_left ι (C : A →+* MvPolynomial σ A) X P
  rw [eval₂_eta] at this
  exact this.symm
end Formalism.DworkPowerSeriesWeights
