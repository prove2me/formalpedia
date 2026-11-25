-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.kHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:22:25.739503+00:00
-- url     : https://prove2.me/submissions/84e200c2-b053-47c3-bd90-e62c3dfb8967

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaSt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CompInsertNthEq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RemoveNthSuccVecCons
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KDKDelApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvarianceContraction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AlternatingMapEqZeroOfSpan
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KugaAbsHolds
import Theorems.Thm_PositivityTheory_Rg_Cz_kDel_kD
import Theorems.Thm_PositivityTheory_Rg_Cz_kInv_sum
import Theorems.Thm_GlobalTheory_CompanionTheory_KDelFormula_kDel_kD


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Fin Function
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M]
namespace PositivityTheory.Rg.Cz
theorem _root_.solution {β γ : Type} [Fintype β] [Fintype γ] (b : β → P) (a r : P →ₗ[ℝ] Module.End ℂ M)
    (a' r' : γ → Module.End ℂ M) (D : γ → P →ₗ[ℝ] P) (c : β → β → γ → ℝ)
    (har : ∀ X Y, Commute (a X) (r Y)) (ha'r' : ∀ k, Commute (a' k) (r' k))
    (hca : ∀ i j, a (b i) * a (b j) - a (b j) * a (b i) = ∑ k, (c i j k : ℂ) • a' k)
    (hcr : ∀ i j, r (b i) * r (b j) - r (b j) * r (b i) = ∑ k, (c i j k : ℂ) • r' k)
    (hc : ∀ i j k, c j i k = -c i j k) (hD : ∀ k j, D k (b j) = ∑ i, c i j k • b i)
    {q : ℕ} (ω : P [⋀^Fin q]→ₗ[ℝ] M)
    (hω : ∀ k (Y : Fin q → P), (a' k + r' k) (ω Y) = ∑ s, ω (Function.update Y s (D k (Y s))))
    (J : Fin q → β) :
    kDel (r - a) b (kD (a + r) ω) (b ∘ J) +
      ∑ s, ∑ i, (a + r) (b (J s)) ((r - a) (b i) (ω (Function.update (b ∘ J) s (b i)))) =
    ((∑ i, r (b i) * r (b i) - ∑ k, r' k * r' k) - (∑ i, a (b i) * a (b i) - ∑ k, a' k * a' k) :
      Module.End ℂ M) (ω (b ∘ J)) := by
  have hcomm : ∀ j i, (a + r) (b j) * (r - a) (b i) - (r - a) (b i) * (a + r) (b j) =
      ∑ k, (c j i k : ℂ) • (r' k - a' k) := by
    intro j i
    have e1 := (har (b j) (b i)).eq
    have e2 := (har (b i) (b j)).eq
    have h : (a + r) (b j) * (r - a) (b i) - (r - a) (b i) * (a + r) (b j) -
        ((r (b j) * r (b i) - r (b i) * r (b j)) - (a (b j) * a (b i) - a (b i) * a (b j))) =
        (a (b j) * r (b i) - r (b i) * a (b j)) - (r (b j) * a (b i) - a (b i) * r (b j)) := by
      simp only [LinearMap.add_apply, LinearMap.sub_apply]
      noncomm_ring
    rw [e1, e2, sub_self, sub_self, sub_zero, sub_eq_zero] at h
    rw [h, hcr, hca, ← Finset.sum_sub_distrib]
    simp only [smul_sub]
  have hsq : ∀ i, (r - a) (b i) * (a + r) (b i) = r (b i) * r (b i) - a (b i) * a (b i) := by
    intro i
    have e := (har (b i) (b i)).eq
    simp only [LinearMap.add_apply, LinearMap.sub_apply, mul_add, sub_mul, e]
    abel
  have hsq' : ∀ k, (r' k - a' k) * (a' k + r' k) = r' k * r' k - a' k * a' k := by
    intro k
    have e := (ha'r' k).eq
    simp only [mul_add, sub_mul, e]
    abel
  have hinv := kInv_sum b D c (fun k => a' k + r' k) hc hD ω hω
  rw [kDel_kD]
  generalize a + r = L at hcomm hsq ⊢
  generalize r - a = L' at hcomm hsq ⊢
  have step1 : ∑ i, L' (b i) (L (b i) (ω (b ∘ J))) -
      ∑ t, ∑ i, L' (b i) (L ((b ∘ J) t) (ω (Function.update (b ∘ J) t (b i)))) +
      ∑ s, ∑ i, L (b (J s)) (L' (b i) (ω (Function.update (b ∘ J) s (b i)))) =
      ∑ i, (L' (b i) * L (b i)) (ω (b ∘ J)) +
      ∑ s, ∑ i, (L (b (J s)) * L' (b i) - L' (b i) * L (b (J s)))
        (ω (Function.update (b ∘ J) s (b i))) := by
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Finset.sum_sub_distrib, Function.comp_apply]
    abel
  rw [step1]
  simp_rw [hsq, hcomm]
  have step2 : ∀ s i, (∑ k, (c (J s) i k : ℂ) • (r' k - a' k)) (ω (Function.update (b ∘ J) s (b i))) =
      ∑ k, (r' k - a' k) ((c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i))) := by
    intro s i
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, map_smul]
  simp_rw [step2]
  have step3 : ∑ s, ∑ i, ∑ k, (r' k - a' k) ((c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i))) =
      ∑ k, ∑ s, ∑ i, (r' k - a' k) ((c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i))) := by
    calc _ = ∑ s, ∑ k, ∑ i, (r' k - a' k) ((c (J s) i k : ℂ) • ω (Function.update (b ∘ J) s (b i))) :=
          Finset.sum_congr rfl fun s _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [step3]
  simp_rw [← map_sum, hinv, map_neg, ← Module.End.mul_apply, hsq']
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  abel
end PositivityTheory.Rg.Cz
