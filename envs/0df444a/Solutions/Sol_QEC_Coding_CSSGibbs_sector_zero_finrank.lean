-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.sector_zero_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:40:29.210492+00:00
-- url     : https://prove2.me/submissions/acf8a534-47dc-410a-9849-eba16cdd9ac7

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Projectors
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Spectrum
import Theorems.Thm_QEC_Coding_CSSGibbs_checkRank_eq_rowDimension
import Theorems.Thm_QEC_Coding_CSSGibbs_sector_zero_eq_code
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSQuantumCodeOfDualLe_finrank_carrier


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.CSSGibbs
open Classical PauliSymplectic StabilizerCode Semantics
open scoped BigOperators
variable {ι κP κQ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κP] [Fintype κQ] [DecidableEq κP] [DecidableEq κQ]
variable (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
  (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
  (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_ea4515a18e_14
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_ea4515a18e_15
namespace QEC.Coding.CSSGibbs
theorem _root_.solution : Module.finrank ℂ (sector P Q horth 0) = multiplicity P Q := by
  rw [sector_zero_eq_code]
  rw [binaryCSSQuantumCodeOfDualLe_finrank_carrier]
  rw [multiplicity, checkRank_eq_rowDimension P, checkRank_eq_rowDimension Q]
  congr 1
  change Fintype.card ι - Dimension (parityCheckRowCode Q) - Dimension (parityCheckRowCode P) = _
  omega
end QEC.Coding.CSSGibbs
