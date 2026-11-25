-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_ProjectionFormulaDegree_proof_0aacacc92e0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:06:07.232611+00:00
-- url     : https://prove2.me/submissions/120be7cb-2d4b-4464-8aac-407c47c0979d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForward
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_rename_fd9a6cb3fd55
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiProjPrime_contractPrime_7e3d9fd91401
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_map_homFracDegZero_le_99e71cc4273e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_sub_2c1b4682dd90
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRational_proof_c27e72dcc134
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ExistsForm_proof_d5dace6f400d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_cycEval_ratDiv_d916b441ca86


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace ProjectionFormulaDegree
theorem _root_.solution (h1 : CutRational.Statement.{u})
    (h2 : IntNumBase.Statement.{u}) (h3 : ProjectionFormulaContracted.Statement.{u})
    (h4 : DivPushForward.Statement.{u}) : ProjectionFormulaDegree.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n
  induction n generalizing P' with
  | zero =>
    intro hdim hdimP bs
    have := hP'.isPrime
    refine ⟨map_homFracDegZero_le j ι' P', ?_⟩
    have hP := isMultiProjPrime_contractPrime j ι' hP'
    have e1 : (fun i : Fin 0 => pullDeg j (bs i)) = ![] := Subsingleton.elim _ _
    have e2 : bs = ![] := Subsingleton.elim _ _
    rw [e1, e2, (h2 F K' ι' P' hP' hdim).2, (h2 F K _ _ hP hdimP).2,
      ← IntermediateField.finrank_bot_mul_relfinrank (map_homFracDegZero_le j ι' P'),
      ← (IntermediateField.equivMap _ (contractFracMap j P')).toLinearEquiv.finrank_eq]
    unfold relDeg
    push_cast
    ring
  | succ n ih =>
    intro hdim hdimP bs
    have := hP'.isPrime
    refine ⟨map_homFracDegZero_le j ι' P', ?_⟩
    have hP := isMultiProjPrime_contractPrime j ι' hP'
    obtain ⟨bf, bg, f, g, hf, hg, hfP, hgP, hb⟩ :=
      ExistsForm.proof F K (fun k => ι' (j k)) (contractPrime j P') hP (bs (Fin.last n))
    have hbs : bs = Fin.snoc (α := fun _ => K → ℤ) (Fin.init bs) (fun k => (bf k : ℤ) - bg k) := by
      rw [hb, Fin.snoc_init_self]
    have hpull : (fun i => pullDeg j (bs i)) = Fin.snoc (α := fun _ => K' → ℤ)
        (fun i => pullDeg j (Fin.init bs i))
        (fun k' => ((Function.extend j bf 0 k' : ℕ) : ℤ) - ((Function.extend j bg 0 k' : ℕ) : ℤ)) := by
      rw [← pullDeg_sub, hb]
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Fin.snoc_last]
      · simp only [Fin.snoc_castSucc, Fin.init]
    have hcutP : intNum F (contractPrime j P') bs =
        cycEval (fun W => intNum F W (Fin.init bs)) (ratDiv (contractPrime j P') f g) := by
      conv_lhs => rw [hbs]
      exact h1 F K _ _ hP n hdimP bf bg f g hf hg hfP hgP (Fin.init bs)
    have hcutP' := h1 F K' ι' P' hP' n hdim _ _ (rename (blockIncl j ι') f)
      (rename (blockIncl j ι') g) (isMultiHomog_rename j ι' hf) (isMultiHomog_rename j ι' hg)
      hfP hgP (fun i => pullDeg j (Fin.init bs i))
    have hyp1 : ∀ W' (hW' : IsMultiProjPrime W'), relDim W' = (n : ℕ) →
        relDim (contractPrime j W') = (n : ℕ) →
        haveI := hW'.isPrime
        intNum F W' (fun i => pullDeg j (Fin.init bs i)) =
          relDeg j W' * intNum F (contractPrime j W') (Fin.init bs) :=
      fun W' hW' hd hc => (ih W' hW' hd hc (Fin.init bs)).2
    have hyp2 : ∀ W', IsMultiProjPrime W' → relDim W' = (n : ℕ) →
        relDim (contractPrime j W') < (n : ℕ) →
        intNum F W' (fun i => pullDeg j (Fin.init bs i)) = 0 :=
      fun W' hW' hd hlt => h3 F K K' j ι' W' hW' n hd hlt (Fin.init bs)
    have hpf := h4 F K K' j ι' P' hP' n hdim hdimP bf f hf hfP (fun W' => intNum F W' (fun i => pullDeg j (Fin.init bs i)))
      (fun W => intNum F W (Fin.init bs)) hyp1 hyp2
    have hpg := h4 F K K' j ι' P' hP' n hdim hdimP bg g hg hgP (fun W' => intNum F W' (fun i => pullDeg j (Fin.init bs i)))
      (fun W => intNum F W (Fin.init bs)) hyp1 hyp2
    rw [hpull, hcutP', hcutP, cycEval_ratDiv, cycEval_ratDiv, mul_sub, hpf, hpg]
end ProjectionFormulaDegree
end GroundTheory.Heights₂.Heights.FieldNumbers
