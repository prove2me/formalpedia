-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ExceptionalComparison_proof_d765768ef0e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:04:30.39769+00:00
-- url     : https://prove2.me/submissions/548f24a9-a5d2-4a54-b567-581ec5ea52ec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ComapLiftFormConstChartPrimeExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivCycleEqZeroOfNotMem
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DivCycleMul_proof_5282581d8898
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultAtPrimeAtMinimal_proof_af70a5a37a53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_aeval_blowUpSubst_liftForm_4b99591f2332
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUp_relation_be19b3539eff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_divCycle_congr_of_sub_mem_56ff166eaee6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_form_mem_of_divCycle_ne_zero_bfda24507b35

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section
section Helpers
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
private theorem divCycle_eq_zero_of_not_mem' {P W : Ideal (MRing ι R)} {x : MRing ι R} (h : x ∉ W) :
    divCycle P x W = 0 := by
  by_contra h'
  exact h (form_mem_of_divCycle_ne_zero h')
private theorem divCycle_nonneg' (P : Ideal (MRing ι R)) (x : MRing ι R) (W : Ideal (MRing ι R)) :
    0 ≤ divCycle P x W := by
  unfold divCycle
  split_ifs <;> positivity
private theorem facts_of_divCycle_ne_zero' {P W : Ideal (MRing ι R)} {x : MRing ι R}
    (h : divCycle P x W ≠ 0) : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W := by
  unfold divCycle at h
  split_ifs at h with hc
  · exact hc
  · exact absurd rfl h
end Helpers
section Rel
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {R : Type u} [CommRing R]
  [IsNoetherianRing R]
private theorem ratDiv_eq_of_rel {P W : Ideal (MRing ι R)} (hP : P.IsPrime) (hPW : P ≤ W)
    {f g a v : MRing ι R} (hf : f ∉ P) (hg : g ∉ P) (ha : a ∉ W) (h : a * f - v * g ∈ P) :
    v ∉ P ∧ ratDiv P f g W = divCycle P v W := by
  have haP : a ∉ P := fun h' => ha (hPW h')
  have hv : v ∉ P := by
    intro hv
    have e : a * f = (a * f - v * g) + v * g := by ring
    have h1 : a * f ∈ P := by rw [e]; exact P.add_mem h (P.mul_mem_right _ hv)
    exact (hP.mem_or_mem h1).elim haP hf
  refine ⟨hv, ?_⟩
  have e1 := congrFun (divCycle_congr_of_sub_mem h) W
  rw [DivCycleMul.proof R K ι P a f hP haP hf, DivCycleMul.proof R K ι P v g hP hv hg] at e1
  simp only [Pi.add_apply] at e1
  rw [divCycle_eq_zero_of_not_mem' ha] at e1
  unfold ratDiv
  linarith
end Rel
section Proof
end Proof
end
end GroundTheory.Heights₂.Heights.NumbersDVR
end

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace ExceptionalComparison
theorem _root_.solution (h₁ : BlowUpDecomposition.Statement.{u}) (h₂ : BlowUpOrderLe.Statement.{u})
    (h₃ : ExceptionalContraction.Statement.{u}) : ExceptionalComparison.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hH e hce m hm hmP hmH G' hϖG' hY₀ hE
  obtain ⟨hQm, -, hsQ, hY₀Q, hD₁, -, -, -⟩ :=
    h₁ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH e hce m hm hmP hmH
  have hG := h₃ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH e hce m hm hmP hmH G' hϖG' hY₀ hE
  set Q := blowUpOf P (blowUpGens s g f m e) with hQdef
  set G := G'.comap (liftForm (J := BlowUpIdx ι)) with hGdef
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hQp : Q.IsPrime := hQm.multiProj.isPrime
  obtain ⟨hG'min, hG'rel⟩ := facts_of_divCycle_ne_zero' hY₀.ne'
  have hGp : G.IsPrime := hG.1.1
  have hPG : P ≤ G := le_sup_left.trans hG.1.2
  have hGrel : IsRelevant G := by
    intro k
    obtain ⟨i, hi⟩ := hG'rel (some k)
    refine ⟨i, fun h => hi ?_⟩
    rw [hGdef, Ideal.mem_comap] at h
    simpa [liftForm, rename_X] using h
  have hlift : ∀ {p : MRing ι O}, p ∉ P → liftForm (J := BlowUpIdx ι) p ∉ Q := by
    intro p hp h
    rw [hQdef, blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm, Polynomial.C_eq_zero,
      Ideal.Quotient.eq_zero_iff_mem] at h
    exact hp h
  have hliftP : ∀ {p : MRing ι O}, p ∈ P → liftForm (J := BlowUpIdx ι) p ∈ Q := by
    intro p hp
    rw [hQdef, blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm,
      Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
  have hfP : f ∉ P := hD.1.num_not_mem
  have hgP : g ∉ P := hD.1.den_not_mem
  have hY₁Q : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ Q := hD₁.1.num_not_mem
  have hmul := DivCycleMul.proof O (Option K) (extIdx ι (BlowUpIdx ι)) Q
  have hnm : ∀ {x y}, x ∉ Q → y ∉ Q → x * y ∉ Q := fun hx hy h => (hQp.mem_or_mem h).elim hx hy

  have e1 := congrFun (divCycle_congr_of_sub_mem (blowUp_relation P s g f m e)) G'
  rw [map_mul, hmul _ _ hQp (hnm (hlift hsP) (hlift hgP)) hY₁Q, hmul _ _ hQp (hlift hsP) (hlift hgP),
    hmul _ _ hQp (hlift (fun h => (hPp.mem_or_mem h).elim hfP hmP)) hY₀Q] at e1
  simp only [Pi.add_apply] at e1
  have eE : ratDiv Q (liftForm (f * m)) (liftForm g * newVar (some none)) G' =
      ratDiv Q (liftForm f) (liftForm g) G' - ratDiv Q (newVar (some none)) (liftForm m) G' := by
    unfold ratDiv
    rw [map_mul, hmul _ _ hQp (hlift hfP) (hlift hmP), hmul _ _ hQp (hlift hgP) hY₁Q]
    simp only [Pi.add_apply]
    ring
  have eE' : ratDiv Q (liftForm (f * m)) (liftForm g * newVar (some none)) G' =
      divCycle Q (liftForm s) G' - divCycle Q (newVar none) G' := by
    unfold ratDiv
    rw [hmul _ _ hQp (hlift hgP) hY₁Q]
    simp only [Pi.add_apply]
    linarith

  have hD₁G' : 0 ≤ ratDiv Q (newVar (some none)) (liftForm m) G' := by
    by_cases h0 : ratDiv Q (newVar (some none)) (liftForm m) G' = 0
    · exact h0.ge
    have hW : G' ∈ (Q ⊔ Ideal.span {newVar (some none)}).minimalPrimes ∧ IsRelevant G' ∨
        G' ∈ (Q ⊔ Ideal.span {liftForm m}).minimalPrimes ∧ IsRelevant G' := by
      unfold ratDiv at h0
      by_cases h1 : divCycle Q (newVar (some none)) G' = 0
      · right; exact facts_of_divCycle_ne_zero' (fun h2 => h0 (by rw [h1, h2, sub_zero]))
      · left; exact facts_of_divCycle_ne_zero' h1
    have hW' : G'.IsPrime ∧ Q ≤ G' ∧ IsRelevant G' := by
      rcases hW with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1.1.1, le_sup_left.trans h1.1.2, h2⟩
      · exact ⟨h1.1.1, le_sup_left.trans h1.1.2, h2⟩
    obtain ⟨a, v, ha, hrel⟩ := hD₁.2 G' hW'.1 hW'.2.1 hW'.2.2
    have := ratDiv_eq_of_rel hQp hW'.2.1 hY₁Q (hlift hmP) ha hrel
    rw [this.2]
    exact divCycle_nonneg' _ _ _

  obtain ⟨a, v, haG, hrelP⟩ := hD.2 G hGp hPG hGrel
  obtain ⟨hvP, hfgG⟩ := ratDiv_eq_of_rel hPp hPG hfP hgP haG hrelP
  have hrelQ : liftForm a * liftForm f - liftForm v * liftForm g ∈ Q := by
    have := hliftP hrelP
    rwa [map_sub, map_mul, map_mul] at this
  have haG' : liftForm (J := BlowUpIdx ι) a ∉ G' := fun h => haG (by rw [hGdef, Ideal.mem_comap]; exact h)
  have hQG' : Q ≤ G' := le_sup_left.trans hG'min.1.2
  obtain ⟨-, hfgG'⟩ := ratDiv_eq_of_rel hQp hQG' (hlift hfP) (hlift hgP) haG' hrelQ

  have hs' := h₂ O K ι (BlowUpIdx ι) P hPp (blowUpGens s g f m e) G' (newVar none) hY₀Q hG'min hG'rel
    s hsP hG s hsP
  have hv' := h₂ O K ι (BlowUpIdx ι) P hPp (blowUpGens s g f m e) G' (newVar none) hY₀Q hG'min hG'rel
    s hsP hG v hvP
  refine ⟨G, ?_, ?_, ?_⟩
  · rw [hGdef, Ideal.mem_comap]
    simpa [liftForm] using hϖG'
  · rw [eE']
    linarith
  · rw [eE, hfgG', hfgG]
    linarith
end ExceptionalComparison
end GroundTheory.Heights₂.Heights.NumbersDVR
