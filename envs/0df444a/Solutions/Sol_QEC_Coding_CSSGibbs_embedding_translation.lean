-- Prove2me | solution 1 for QEC.Coding.CSSGibbs.embedding_translation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:45:23.09174+00:00
-- url     : https://prove2.me/submissions/34b3fce0-a1e8-4f2a-a794-4232c57b00e2

import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Selection
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSSyndrome_eq_classicalSyndromes


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
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_22196e9987_17
attribute [local instance] QEC.Coding.CSSGibbs._p2m_local_instance_22196e9987_18
include horth
namespace QEC.Coding.CSSGibbs
theorem _root_.solution (E : Binary ι) (s : Realizable P Q) :
    realizableEmbedding P Q (jointTranslation P Q E s) =
      realizableEmbedding P Q s + stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E := by
  rw [binaryCSSSyndrome_eq_classicalSyndromes P Q horth E]
  funext j
  cases j <;> rfl
end QEC.Coding.CSSGibbs
