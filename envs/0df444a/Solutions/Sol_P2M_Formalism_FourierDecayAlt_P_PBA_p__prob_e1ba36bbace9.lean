-- Prove2me | solution 1 for P2M_Formalism_FourierDecayAlt_P_PBA_p__prob_e1ba36bbace9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:35:10.199734+00:00
-- url     : https://prove2.me/submissions/39b872d3-c7c1-45c8-a1aa-8fbb06c9f4ad

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_mem_Wb
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_pw_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_pw_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_supp_word
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
variable {S}
variable {A : Finset (Fin S.f)} {w : S.W} {n : ℕ} {U : Fin S.f → Finset (List C.Letter)}
  {θ : Fin S.f → List C.Letter → ℝ}
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution (hP : ∀ v ∈ A, TB.IsProb (U v) (θ v))
    (hU : ∀ v ∈ A, ∀ a ∈ U v, D.AdmAt S v a ∧ a.length ≤ n) (hw : w.1.cnt ≤ n) (hn : n ≤ S.Ntop) :
    TB.IsProb (S.base.Wb n) (pθ S A w θ) := by
  classical
  refine ⟨fun w' => Finset.prod_nonneg fun v _ => pw_nonneg hP v _, fun w' hw' => ?_, ?_⟩
  · by_contra h0
    apply hw'
    have hg : w'.1 ∈ Fintype.piFinset (supp S A w U) := by
      rw [Fintype.mem_piFinset]
      intro v
      refine pw_ne_zero hP fun h1 => h0 ?_
      exact Finset.prod_eq_zero (Finset.mem_univ v) h1
    exact mem_Wb S (supp_word hU hw hn hg).2
  · have := expand hP hU hw hn (fun _ _ => 1)
    simp only [mul_one, Finset.prod_const_one] at this
    have e : ∏ v, (if v ∈ A then ∑ a ∈ U v, (θ v a : ℂ) else 1) = 1 := by
      refine Finset.prod_eq_one fun v _ => ?_
      split_ifs with hv
      · exact_mod_cast (hP v hv).2.2
      · rfl
    rw [e] at this
    exact_mod_cast this
end Formalism.FourierDecayAlt.P.PBA
