-- Prove2me | solution 1 for TaoAnDCA.LocalOpt.theorem_3_2_ii
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T02:25:29.070633+00:00
-- url     : https://prove2.me/submissions/2bcba00f-6da8-4459-9b0f-85ea58ca2375

import Mathlib
import Definitions.Def_TaoAnDCA_LocalOpt_Setting

open Filter Topology


namespace TaoAnDCA.LocalOpt

/-- value of the conjugate at a subgradient -/
theorem h33_conj_of_subgrad {n : ℕ} (θ : EuclideanSpace ℝ (Fin n) → EReal)
    (hθ : ∀ x, θ x ≠ ⊥) (x y : EuclideanSpace ℝ (Fin n)) (a : ℝ) (hax : θ x = (a : EReal))
    (hy : y ∈ TaoAnDCA.GlobalOpt.subdiff θ x) :
    CondatPD.FinDim.conj θ y = ((inner ℝ y x - a : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro s
    have h1 := hy.2 s
    rw [hax] at h1
    cases hs : θ s with
    | bot => exact absurd hs (hθ s)
    | top => simp
    | coe c =>
      rw [hs] at h1
      have h2 : a + inner ℝ y (s - x) ≤ c := by exact_mod_cast h1
      rw [inner_sub_right] at h2
      rw [← EReal.coe_sub]
      exact_mod_cast (by linarith)
  · refine le_trans ?_ (le_iSup _ x)
    rw [hax]
    exact le_rfl

theorem h33_conj_ge {n : ℕ} (θ : EuclideanSpace ℝ (Fin n) → EReal) (x y : EuclideanSpace ℝ (Fin n))
    (c : ℝ) (hc : θ x = (c : EReal)) :
    ((inner ℝ y x - c : ℝ) : EReal) ≤ CondatPD.FinDim.conj θ y := by
  refine le_trans ?_ (le_iSup _ x)
  rw [hc]
  exact le_rfl

theorem h33_thm32ii_core {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hgh : TaoAnDCA.GlobalOpt.DCStanding g h)
    (xs ys : EuclideanSpace ℝ (Fin n)) (hys : ys ∈ TaoAnDCA.GlobalOpt.subdiff g xs ∩ TaoAnDCA.GlobalOpt.subdiff h xs)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : U ∈ 𝓝 xs)
    (hcond : ∀ x ∈ U ∩ TaoAnDCA.GlobalOpt.effDom g, ∃ y ∈ TaoAnDCA.GlobalOpt.subdiff h x,
      TaoAnDCA.GlobalOpt.dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) ys ≤
        TaoAnDCA.GlobalOpt.dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) y) :
    TaoAnDCA.GlobalOpt.dcSub g h xs ≠ ⊤ ∧ TaoAnDCA.GlobalOpt.dcSub g h xs ≠ ⊥ ∧
    ∀ x ∈ U ∩ TaoAnDCA.GlobalOpt.effDom g, TaoAnDCA.GlobalOpt.dcSub g h xs ≤ TaoAnDCA.GlobalOpt.dcSub g h x := by
  have hg : ∀ x, g x ≠ ⊥ := hgh.g_mem.1
  have hh : ∀ x, h x ≠ ⊥ := hgh.h_mem.1
  obtain ⟨⟨hgs, _⟩, ⟨hhs, _⟩⟩ := (⟨hys.1, hys.2⟩ : _ ∧ _)
  obtain ⟨a, ha⟩ : ∃ a : ℝ, g xs = (a : EReal) := ⟨(g xs).toReal, (EReal.coe_toReal hgs (hg xs)).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, h xs = (b : EReal) := ⟨(h xs).toReal, (EReal.coe_toReal hhs (hh xs)).symm⟩
  have hcg := h33_conj_of_subgrad g hg xs ys a ha hys.1
  have hch := h33_conj_of_subgrad h hh xs ys b hb hys.2
  have hval : TaoAnDCA.GlobalOpt.dcSub g h xs = ((a - b : ℝ) : EReal) := by
    unfold TaoAnDCA.GlobalOpt.dcSub
    rw [ha, hb]; simp [← EReal.coe_sub]
  have hvalD : TaoAnDCA.GlobalOpt.dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) ys
      = ((a - b : ℝ) : EReal) := by
    unfold TaoAnDCA.GlobalOpt.dcSub
    rw [hch, hcg]
    simp only [EReal.coe_ne_top, if_false, ← EReal.coe_sub]
    congr 1; ring
  refine ⟨by rw [hval]; exact EReal.coe_ne_top _, by rw [hval]; exact EReal.coe_ne_bot _, ?_⟩
  intro x hx
  obtain ⟨y, hy, hyc⟩ := hcond x hx
  have hxg : g x ≠ ⊤ := hx.2
  have hxh : h x ≠ ⊤ := hgh.dom_g_sub hx.2
  obtain ⟨c, hc⟩ : ∃ c : ℝ, g x = (c : EReal) := ⟨(g x).toReal, (EReal.coe_toReal hxg (hg x)).symm⟩
  obtain ⟨d, hd⟩ : ∃ d : ℝ, h x = (d : EReal) := ⟨(h x).toReal, (EReal.coe_toReal hxh (hh x)).symm⟩
  have hchy := h33_conj_of_subgrad h hh x y d hd hy
  have hcgy := h33_conj_ge g x y c hc
  have hvx : TaoAnDCA.GlobalOpt.dcSub g h x = ((c - d : ℝ) : EReal) := by
    unfold TaoAnDCA.GlobalOpt.dcSub
    rw [hc, hd]; simp [← EReal.coe_sub]
  have hle : TaoAnDCA.GlobalOpt.dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) y
      ≤ ((c - d : ℝ) : EReal) := by
    unfold TaoAnDCA.GlobalOpt.dcSub
    rw [hchy]
    simp only [EReal.coe_ne_top, if_false]
    calc ((inner ℝ y x - d : ℝ) : EReal) - CondatPD.FinDim.conj g y
        ≤ ((inner ℝ y x - d : ℝ) : EReal) - ((inner ℝ y x - c : ℝ) : EReal) :=
          EReal.sub_le_sub le_rfl hcgy
      _ = ((c - d : ℝ) : EReal) := by rw [← EReal.coe_sub]; congr 1; ring
  rw [hval, hvx]
  rw [hvalD] at hyc
  exact hyc.trans hle

theorem h33_thm32ii_full {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hgh : TaoAnDCA.GlobalOpt.DCStanding g h)
    (xs ys : EuclideanSpace ℝ (Fin n)) (hys : ys ∈ TaoAnDCA.GlobalOpt.subdiff g xs ∩ TaoAnDCA.GlobalOpt.subdiff h xs)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : U ∈ 𝓝 xs)
    (hdom : U ∩ TaoAnDCA.GlobalOpt.effDom g ⊆ {x | (TaoAnDCA.GlobalOpt.subdiff h x).Nonempty})
    (hcond : ∀ x ∈ U ∩ TaoAnDCA.GlobalOpt.effDom g, ∃ y ∈ TaoAnDCA.GlobalOpt.subdiff h x,
      TaoAnDCA.GlobalOpt.dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) ys ≤
        TaoAnDCA.GlobalOpt.dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) y) :
    IsDCLocalMin g h xs ∧ ∀ x ∈ U ∩ TaoAnDCA.GlobalOpt.effDom g, TaoAnDCA.GlobalOpt.dcSub g h xs ≤ TaoAnDCA.GlobalOpt.dcSub g h x := by
  obtain ⟨h1, h2, h3⟩ := h33_thm32ii_core g h hgh xs ys hys U hU hcond
  refine ⟨⟨h1, h2, U, hU, fun z hz => ?_⟩, h3⟩
  by_cases hgz : g z = ⊤
  · have : TaoAnDCA.GlobalOpt.dcSub g h z = ⊤ := by
      unfold TaoAnDCA.GlobalOpt.dcSub; simp [hgz]
    rw [this]; exact le_top
  · exact h3 z ⟨hz, hgz⟩

end TaoAnDCA.LocalOpt

open TaoAnDCA.LocalOpt


theorem solution {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal) (hgh : TaoAnDCA.GlobalOpt.DCStanding g h)
    (xs ys : EuclideanSpace ℝ (Fin n)) (hys : ys ∈ TaoAnDCA.GlobalOpt.subdiff g xs ∩ TaoAnDCA.GlobalOpt.subdiff h xs)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : U ∈ 𝓝 xs)
    (hdom : U ∩ TaoAnDCA.GlobalOpt.effDom g ⊆ {x | (TaoAnDCA.GlobalOpt.subdiff h x).Nonempty})
    (hcond : ∀ x ∈ U ∩ TaoAnDCA.GlobalOpt.effDom g, ∃ y ∈ TaoAnDCA.GlobalOpt.subdiff h x,
      TaoAnDCA.GlobalOpt.dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) ys ≤
        TaoAnDCA.GlobalOpt.dcSub (CondatPD.FinDim.conj h) (CondatPD.FinDim.conj g) y) :
    IsDCLocalMin g h xs ∧ ∀ x ∈ U ∩ TaoAnDCA.GlobalOpt.effDom g, TaoAnDCA.GlobalOpt.dcSub g h xs ≤ TaoAnDCA.GlobalOpt.dcSub g h x := by
  exact h33_thm32ii_full g h hgh xs ys hys U hU hdom hcond
