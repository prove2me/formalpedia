-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_proof_9857bc3e5586
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:06:38.524362+00:00
-- url     : https://prove2.me/submissions/c762dc3f-881b-4c66-83f8-7199c28f2b42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingNoetherian
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_component_form_mul_76a1836436b5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_img_eq_zero_iff_1a7b10f3ef75
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_img_component_congr_4af0000f3a87
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_img_ne_zero_c423baf51a0e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingNoetherian_quot_mem_6be65faba13b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open HomLocRingNoetherian
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace HomLocRingNoetherian
theorem _root_.solution (hmem : HomLocRingMem.Statement.{u}) :
    HomLocRingNoetherian.Statement.{u} := by
  intro R _ _ K _ _ ι _ P W _ hP hW _ hPW
  classical
  set S := MRing ι R
  set D := S ⧸ P
  set F := FractionRing D

  let T : Submonoid S :=
    { carrier := {s | (∃ e, IsMultiHomog s e) ∧ s ∉ W}
      one_mem' := ⟨⟨0, isWeightedHomogeneous_one R _⟩, (Ideal.ne_top_iff_one W).mp hW.ne_top⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨⟨_, ha.1.choose_spec.mul hb.1.choose_spec⟩, hW.mul_notMem ha.2 hb.2⟩ }
  let T' : Submonoid D := T.map (Ideal.Quotient.mk P)
  have hT' : T' ≤ nonZeroDivisors D := by
    rintro _ ⟨t, ht, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => ht.2 (hPW ?_)
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  let B : Subalgebra D F := Localization.subalgebra F T' hT'
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing T' B inferInstance

  have rep : ∀ y ∈ B, ∃ (h t : S) (e : K → ℕ), IsMultiHomog t e ∧ t ∉ W ∧ y * img P t = img P h := by
    rintro y ⟨a, s, ⟨t, ⟨⟨e, hte⟩, htW⟩, rfl⟩, rfl⟩
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨h, t, e, hte, htW, IsLocalization.mk'_spec _ _ _⟩
  have hAB : ∀ x ∈ homLocRing P W, x ∈ B := by
    intro x hx
    refine (Subring.closure_le (t := B.toSubring)).mpr ?_ hx
    rintro _ ⟨b, f, g, hf, hg, hgW, rfl⟩
    exact ⟨Ideal.Quotient.mk P f, Ideal.Quotient.mk P g, ⟨g, ⟨⟨b, hg⟩, hgW⟩, rfl⟩,
      by rw [IsFractionRing.mk'_eq_div]⟩
  let j : homLocRing P W →+* B :=
    { toFun := fun a => ⟨a, hAB a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

  have key : ∀ (I : Ideal (homLocRing P W)) (z : homLocRing P W), j z ∈ I.map j → z ∈ I := by
    intro I z hz
    let Q : F → Prop := fun y => ∀ (s : S) (e : K → ℕ) (h : S), IsMultiHomog s e → s ∉ W →
      y * img P s = img P h → ∀ (d : K → ℕ) (t : S), IsMultiHomog t d → t ∉ W →
        ∃ a ∈ I, (a : F) = img P (weightedHomogeneousComponent (blockWeight ι) d h) / img P t
    have Q0 : Q 0 := by
      intro s e h _ _ hy d t _ _
      refine ⟨0, I.zero_mem, ?_⟩
      rw [zero_mul, eq_comm, img_eq_zero_iff] at hy
      rw [img_eq_zero_iff.mpr (hP h hy d), zero_div]
      rfl
    have Qadd : ∀ y₁ ∈ B, ∀ y₂ ∈ B, Q y₁ → Q y₂ → Q (y₁ + y₂) := by
      intro y₁ hy₁ y₂ hy₂ Q₁ Q₂ s e h hs hsW hy d t ht htW
      obtain ⟨h₁, t₁, e₁, ht₁, ht₁W, hb₁⟩ := rep y₁ hy₁
      obtain ⟨h₂, t₂, e₂, ht₂, ht₂W, hb₂⟩ := rep y₂ hy₂
      have hσ : IsMultiHomog (s * t₁ * t₂) (e + e₁ + e₂) := (hs.mul ht₁).mul ht₂
      have hσW : s * t₁ * t₂ ∉ W := hW.mul_notMem (hW.mul_notMem hsW ht₁W) ht₂W
      have hτ : IsMultiHomog (t₁ * t₂ * t) ((e₁ + e₂) + d) := (ht₁.mul ht₂).mul ht
      have hτW : t₁ * t₂ * t ∉ W := hW.mul_notMem (hW.mul_notMem ht₁W ht₂W) htW
      obtain ⟨a₁, ha₁I, ha₁⟩ := Q₁ _ _ (h₁ * (s * t₂)) hσ hσW
        (by simp only [map_mul]; rw [← hb₁]; ring) _ _ hτ hτW
      obtain ⟨a₂, ha₂I, ha₂⟩ := Q₂ _ _ (h₂ * (s * t₁)) hσ hσW
        (by simp only [map_mul]; rw [← hb₂]; ring) _ _ hτ hτW
      refine ⟨a₁ + a₂, I.add_mem ha₁I ha₂I, ?_⟩
      have hsum : img P (h₁ * (s * t₂) + h₂ * (s * t₁)) = img P ((t₁ * t₂) * h) := by
        simp only [map_mul, map_add]; rw [← hb₁, ← hb₂, ← hy]; ring
      have hc := img_component_congr hP hsum ((e₁ + e₂) + d)
      rw [component_form_mul (ht₁.mul ht₂), map_add, map_add] at hc
      have h1 := img_ne_zero hPW ht₁W
      have h2 := img_ne_zero hPW ht₂W
      have h3 := img_ne_zero hPW htW
      rw [Subring.coe_add, ha₁, ha₂, ← add_div, hc]
      simp only [map_mul]
      field_simp
    have Qgen : ∀ b ∈ B, ∀ a ∈ I, Q (b * (a : F)) := by
      intro b hb a haI s e h hs hsW hy d t ht htW
      obtain ⟨h₁, t₁, e₁, ht₁, ht₁W, hb₁⟩ := rep b hb
      obtain ⟨c, f, g, hf, hg, hgW, hfg⟩ := (hmem R K ι P W hW hPW a).mp a.2
      have hfg' : (a : F) = img P f / img P g := hfg
      have hg0 := img_ne_zero hPW hgW
      have hfa : img P f = a * img P g := by rw [hfg', div_mul_cancel₀ _ hg0]
      have hrel : img P (f * (h₁ * s)) = img P ((t₁ * g) * h) := by
        simp only [map_mul]; rw [hfa, ← hy, ← hb₁]; ring
      have hc := img_component_congr hP hrel (c + (d + e₁))
      rw [component_form_mul hf, show c + (d + e₁) = (e₁ + c) + d by abel,
        component_form_mul (ht₁.mul hg)] at hc
      have ha' := quot_mem (P := P) (W := W)
        (weightedHomogeneousComponent_isWeightedHomogeneous (d + e₁) (h₁ * s)) (ht.mul ht₁)
        (hW.mul_notMem htW ht₁W)
      refine ⟨a * ⟨_, ha'⟩, I.mul_mem_right _ haI, ?_⟩
      have h1 := img_ne_zero hPW ht₁W
      have h3 := img_ne_zero hPW htW
      rw [Subring.coe_mul, hfg']
      simp only [map_mul] at hc ⊢
      field_simp
      linear_combination hc
    have hspan : ∀ y ∈ I.map j, ∀ b : B, Q ((b : F) * (y : F)) := by
      intro y hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨a, haI, rfl⟩ b
        exact Qgen b b.2 a haI
      · intro b
        simpa using Q0
      · intro y₁ y₂ _ _ Q₁ Q₂ b
        have := Qadd _ (b * y₁).2 _ (b * y₂).2 (Q₁ b) (Q₂ b)
        simpa [mul_add] using this
      · intro c y _ Qy b
        have := Qy (b * c)
        simpa [mul_assoc] using this
    obtain ⟨c, f, g, hf, hg, hgW, hfg⟩ := (hmem R K ι P W hW hPW z).mp z.2
    have hfg' : (z : F) = img P f / img P g := hfg
    have hg0 := img_ne_zero hPW hgW
    obtain ⟨a, haI, ha⟩ := hspan _ hz 1 g c f hg hgW
      (by show 1 * (z : F) * img P g = img P f; rw [one_mul, hfg', div_mul_cancel₀ _ hg0])
      c g hg hgW
    rw [hf.weightedHomogeneousComponent_same, ← hfg'] at ha
    exact (Subtype.ext ha : a = z) ▸ haI
  have hinj : Function.Injective (fun I : Ideal (homLocRing P W) => I.map j) := by
    intro I₁ I₂ h12
    have e : ∀ I : Ideal (homLocRing P W), (I.map j).comap j = I := fun I =>
      le_antisymm (fun z hz => key I z hz) Ideal.le_comap_map
    rw [← e I₁, ← e I₂]
    exact congrArg (Ideal.comap j) h12
  have hmono' : Monotone (fun I : Ideal (homLocRing P W) => I.map j) := fun _ _ h => Ideal.map_mono h
  have hmono : StrictMono (fun I : Ideal (homLocRing P W) => I.map j) :=
    hmono'.strictMono_of_injective hinj
  have : WellFoundedGT (Ideal B) := isNoetherian_iff'.mp (isNoetherianRing_iff.mp inferInstance)
  exact isNoetherianRing_iff.mpr (isNoetherian_iff'.mpr hmono.wellFoundedGT)
end HomLocRingNoetherian
end GroundTheory.Heights₂.Heights.NumbersDVR
