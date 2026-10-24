-- Prove2me | solution 1 for TopkisRation.TimeMono.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T16:04:56.504645+00:00
-- url     : https://prove2.me/submissions/c4a0c0cb-e988-43f7-a892-8bd6d9fc5fb2

import Mathlib
import Definitions.Def_TopkisRation_TimeMono_Model
import Theorems.Thm_TopkisRation_Levels_lemma_2

set_option autoImplicit false

namespace T2Aux

open TopkisRation MeasureTheory Filter Topology

/-- Convex increments are monotone in the base point. -/
theorem conv_inc {ψ : ℝ → ℝ} (hψ : ConvexOn ℝ (Set.Ici 0) ψ) {w z d : ℝ} (hw : 0 ≤ w)
    (hwz : w ≤ z) (hd : 0 ≤ d) : ψ (w + d) - ψ w ≤ ψ (z + d) - ψ z := by
  rcases eq_or_lt_of_le hd with hd0 | hd0
  · subst hd0; simp
  rcases eq_or_lt_of_le hwz with hwz' | hwz'
  · subst hwz'; exact le_rfl
  have mw : w ∈ Set.Ici (0:ℝ) := hw
  have mwd : w + d ∈ Set.Ici (0:ℝ) := by simp only [Set.mem_Ici]; linarith
  have mz : z ∈ Set.Ici (0:ℝ) := by simp only [Set.mem_Ici]; linarith
  have mzd : z + d ∈ Set.Ici (0:ℝ) := by simp only [Set.mem_Ici]; linarith
  have h1 := hψ.secant_mono (a := w) (x := w + d) (y := z + d) mw mwd mzd
    (by linarith) (by linarith) (by linarith)
  have h2 := hψ.secant_mono (a := z + d) (x := w) (y := z) mzd mw mz
    (by linarith) (by linarith) (by linarith)
  have e1 : w + d - w = d := by ring
  have e2 : (ψ w - ψ (z + d)) / (w - (z + d)) = (ψ (z + d) - ψ w) / (z + d - w) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]; ring
  have e3 : (ψ z - ψ (z + d)) / (z - (z + d)) = (ψ (z + d) - ψ z) / d := by
    rw [div_eq_div_iff (by linarith) (by linarith)]; ring
  rw [e1] at h1
  rw [e2, e3] at h2
  have h3 := h1.trans h2
  rwa [div_le_div_iff_of_pos_right hd0] at h3

/-- From the hypothesis `p₁ + D⁺h ≤ p₀` on `[0,∞)`, increments of the convex `h` are at most
`(p₀ - p₁)` per unit. -/
theorem h_inc {h : ℝ → ℝ} (hc : ConvexOn ℝ (Set.Ici 0) h) (p₀ p₁ : ℝ)
    (hp : ∀ z : ℝ, 0 ≤ z → (p₁ : EReal) + Levels.rightDeriv h z ≤ (p₀ : EReal))
    {y w : ℝ} (hy : 0 ≤ y) (hyw : y < w) : h w - h y ≤ (p₀ - p₁) * (w - y) := by
  have hwy : 0 < w - y := by linarith
  set s : ℝ := (h w - h y) / (w - y) with hs
  have key : ∀ δ : ℝ, 0 < δ → s ≤ (h (w + δ) - h w) / δ := by
    intro δ hδ
    have my : y ∈ Set.Ici (0:ℝ) := hy
    have mw : w ∈ Set.Ici (0:ℝ) := by simp only [Set.mem_Ici]; linarith
    have mwd : w + δ ∈ Set.Ici (0:ℝ) := by simp only [Set.mem_Ici]; linarith
    have h1 := hc.secant_mono (a := w) (x := y) (y := w + δ) mw my mwd
      (by linarith) (by linarith) (by linarith)
    have e1 : (h y - h w) / (y - w) = s := by
      rw [hs, div_eq_div_iff (by linarith) (by linarith)]; ring
    have e2 : w + δ - w = δ := by ring
    rw [e1, e2] at h1
    exact h1
  have hlim : (s : EReal) ≤ Levels.rightDeriv h w := by
    unfold Levels.rightDeriv
    apply Filter.le_liminf_of_le
    · isBoundedDefault
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact EReal.coe_le_coe_iff.mpr (key δ hδ)
  have h2 : ((p₁ + s : ℝ) : EReal) ≤ (p₀ : EReal) := by
    rw [EReal.coe_add]
    exact (add_le_add le_rfl hlim).trans (hp w (by linarith))
  have h3 : p₁ + s ≤ p₀ := EReal.coe_le_coe_iff.mp h2
  have h4 : s ≤ p₀ - p₁ := by linarith
  rw [hs, div_le_iff₀ hwy] at h4
  exact h4

variable {n : ℕ}

/-- Convexity of `y ↦ g_s(y, 0)` on `[0,∞)` (restriction of Lemma 2's joint convexity). -/
theorem g_line (L : Levels.Model n) (s : ℕ)
    (hc : ConvexOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : Fin n → ℝ)) (fun q => L.g s q.1 q.2)) :
    ConvexOn ℝ (Set.Ici 0) (fun y => L.g s y 0) := by
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  have := hc.2 (x := (x, 0)) (y := (y, 0)) (Set.mk_mem_prod hx (Set.mem_Ici.mpr le_rfl))
    (Set.mk_mem_prod hy (Set.mem_Ici.mpr le_rfl)) ha hb hab
  simpa using this

/-- Pointwise step: with `a_{s+1} = 0`, raising the stock from `z` to `z'` raises
`f_{s+1}(·, B)` by at most the increment of `ψ = h_{s+1} + g_s(·, 0)`. -/
theorem stepB (L : Levels.Model n) (hL : L.Standing) (s : ℕ) (hs : s + 1 ≤ L.k)
    (ha : L.a (s + 1) = 0)
    (hψ : ConvexOn ℝ (Set.Ici 0) (fun y => L.h (s + 1) y + L.g s y 0))
    (z z' : ℝ) (hz : 0 ≤ z) (hzz : z ≤ z') (B : Fin n → ℝ) (hB : 0 ≤ B) :
    L.f (s + 1) z' B - L.f (s + 1) z B ≤
      (L.h (s + 1) z' + L.g s z' 0) - (L.h (s + 1) z + L.g s z 0) := by
  have H := (Levels.lemma_2 L hL (s + 1) hs).2.2.1 (by omega)
  obtain ⟨u, hu, hfu, -⟩ := H z hz B hB
  obtain ⟨u', -, hfu', hmin⟩ := H z' (by linarith) B hB
  obtain ⟨hu0, huB, husum⟩ := hu
  have hfeas : u ∈ Levels.feasible z' B := ⟨hu0, huB, by linarith⟩
  have h1 := hmin u hfeas
  have hS0 : 0 ≤ ∑ j, (B j - u j) := Finset.sum_nonneg (fun j _ => sub_nonneg.mpr (huB j))
  simp only [Levels.Model.obj, ha, zero_smul, Nat.add_sub_cancel] at hfu hfu' h1
  have hc := conv_inc hψ (w := z - ∑ j, (B j - u j)) (z := z) (d := z' - z)
    (by linarith) (by linarith) (by linarith)
  have e1 : z - ∑ j, (B j - u j) + (z' - z) = z' - ∑ j, (B j - u j) := by ring
  have e2 : z + (z' - z) = z' := by ring
  simp only [e1, e2] at hc
  rw [hfu, hfu']
  linarith

/-- Integrated step: `g_{s+1}(·, 0)` increments are bounded by those of `ψ`. -/
theorem stepG (L : Levels.Model n) (hL : L.Standing) (s : ℕ) (hs : s + 1 ≤ L.k)
    (ha : L.a (s + 1) = 0)
    (hψ : ConvexOn ℝ (Set.Ici 0) (fun y => L.h (s + 1) y + L.g s y 0))
    (z z' : ℝ) (hz : 0 ≤ z) (hzz : z ≤ z') :
    L.g (s + 1) z' 0 - L.g (s + 1) z 0 ≤
      (L.h (s + 1) z' + L.g s z' 0) - (L.h (s + 1) z + L.g s z 0) := by
  have hint := (Levels.lemma_2 L hL (s + 1) hs).2.2.2 (by omega)
  have i1 := hint z' (by linarith) 0 le_rfl
  have i0 := hint z hz 0 le_rfl
  have hmem : s + 1 ∈ Finset.Icc 1 L.k := Finset.mem_Icc.mpr ⟨by omega, hs⟩
  have hprob : IsProbabilityMeasure (L.μ (s + 1)) := hL.μ_prob (s + 1) hmem
  have hnn := hL.μ_nonneg (s + 1) hmem
  have hg : ∀ x, L.g (s + 1) x 0 = ∫ y, L.f (s + 1) x (0 + y) ∂(L.μ (s + 1)) := fun x => rfl
  rw [hg, hg, ← integral_sub i1 i0]
  calc ∫ y, (L.f (s + 1) z' (0 + y) - L.f (s + 1) z (0 + y)) ∂(L.μ (s + 1))
      ≤ ∫ _y, ((L.h (s + 1) z' + L.g s z' 0) - (L.h (s + 1) z + L.g s z 0)) ∂(L.μ (s + 1)) := by
        apply integral_mono_ae (i1.sub i0) (integrable_const _)
        filter_upwards [hnn] with y hy
        exact stepB L hL s hs ha hψ z z' hz hzz (0 + y) (by simpa using hy)
    _ = (L.h (s + 1) z' + L.g s z' 0) - (L.h (s + 1) z + L.g s z 0) := by simp

/-- The key comparison: increments of `φ_{t+1}` are bounded by those of `φ_t`. -/
theorem key (L : Levels.Model n) (hL : L.Standing) (t : ℕ) (ht1 : 1 ≤ t)
    (htk : t + 1 ≤ L.k) (ha1 : L.a (t + 1) = 0) (ha0 : L.a t = 0) (j : Fin n)
    (hp : ∀ z : ℝ, 0 ≤ z →
      (L.p (t + 1) j : EReal) + Levels.rightDeriv (L.h (t + 1)) z ≤ (L.p t j : EReal))
    (y w : ℝ) (hy : 0 ≤ y) (hyw : y ≤ w) :
    L.levelObj (t + 1) j w - L.levelObj (t + 1) j y ≤ L.levelObj t j w - L.levelObj t j y := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rcases eq_or_lt_of_le hyw with rfl | hlt
  · simp
  have hmem0 : s + 1 ∈ Finset.Icc 1 L.k := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hmem1 : s + 1 + 1 ∈ Finset.Icc 1 L.k := Finset.mem_Icc.mpr ⟨by omega, htk⟩
  have hψ : ConvexOn ℝ (Set.Ici 0) (fun y => L.h (s + 1) y + L.g s y 0) :=
    (hL.h_convex (s + 1) hmem0).add (g_line L s (Levels.lemma_2 L hL s (by omega)).1.1)
  have G := stepG L hL s (by omega) ha0 hψ y w hy hyw
  have Hh := h_inc (hL.h_convex (s + 1 + 1) hmem1) (L.p (s + 1) j) (L.p (s + 1 + 1) j) hp hy hlt
  simp only [Levels.Model.levelObj, ha1, ha0, zero_smul, Nat.add_sub_cancel]
  have e : (L.p (s + 1) j - L.p (s + 1 + 1) j) * (w - y)
      = L.p (s + 1) j * w - L.p (s + 1) j * y - (L.p (s + 1 + 1) j * w - L.p (s + 1 + 1) j * y) := by
    ring
  linarith

theorem main (L : Levels.Model n) (hL : L.Standing) (t : ℕ) (ht1 : 1 ≤ t)
    (htk : t + 1 ≤ L.k) (ha1 : L.a (t + 1) = 0) (ha0 : L.a t = 0) (j : Fin n)
    (hp : ∀ z : ℝ, 0 ≤ z →
      (L.p (t + 1) j : EReal) + Levels.rightDeriv (L.h (t + 1)) z ≤ (L.p t j : EReal))
    (z₀ z₁ : WithTop ℝ) (hz₀ : Levels.IsCriticalLevel (L.levelObj t j) z₀)
    (hz₁ : Levels.IsCriticalLevel (L.levelObj (t + 1) j) z₁) : z₀ ≤ z₁ := by
  have K := key L hL t ht1 htk ha1 ha0 j hp
  rcases hz₁ with ⟨rfl, -⟩ | ⟨x₁, rfl, hx₁, hmin₁, -⟩
  · exact le_top
  rcases hz₀ with ⟨rfl, hanti⟩ | ⟨x₀, rfl, hx₀, hmin₀, hsmall₀⟩
  · exfalso
    have h1 : L.levelObj t j (x₁ + 1) < L.levelObj t j x₁ :=
      hanti (Set.mem_Ici.mpr hx₁) (Set.mem_Ici.mpr (by linarith)) (by linarith)
    have h2 := K x₁ (x₁ + 1) hx₁ (by linarith)
    have h3 := hmin₁ (x₁ + 1) (by linarith)
    linarith
  · rw [WithTop.coe_le_coe]
    by_contra hlt
    push_neg at hlt
    have hstrict : L.levelObj t j x₀ < L.levelObj t j x₁ := by
      by_contra hge
      push_neg at hge
      have := hsmall₀ x₁ hx₁ (fun w hw => hge.trans (hmin₀ w hw))
      linarith
    have h2 := K x₁ x₀ hx₁ hlt.le
    have h3 := hmin₁ x₀ hx₀
    linarith

/-- The `TimeMono` model viewed as a `Levels` model (identical fields). -/
def toL (M : TimeMono.Model n) : Levels.Model n :=
  ⟨M.k, M.a, M.p, M.h, M.v₁, M.v₂, M.c, M.μ⟩

theorem g_eq (M : TimeMono.Model n) : ∀ t, M.g t = (toL M).g t
  | 0 => rfl
  | t + 1 => by
    funext z b
    simp only [TimeMono.Model.g, Levels.Model.g]
    rw [g_eq M t]
    rfl

theorem levelObj_eq (M : TimeMono.Model n) (t : ℕ) (j : Fin n) :
    M.levelObj t j = (toL M).levelObj t j := by
  funext w
  simp only [TimeMono.Model.levelObj, Levels.Model.levelObj, g_eq]
  rfl

theorem standing (M : TimeMono.Model n) (hM : M.Standing) : (toL M).Standing :=
  ⟨hM.a_nonneg, hM.h_convex, hM.h_cont, hM.v₁_convex, hM.v₁_cont, hM.v₂_convex, hM.v₂_cont,
    hM.v₂_slope, hM.p_nonneg, hM.p_mono, hM.μ_prob, hM.μ_nonneg, hM.μ_mean⟩

end T2Aux

open TopkisRation.TimeMono in
theorem solution {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ) (ht1 : 1 ≤ t)
    (htk : t + 1 ≤ M.k) (ha1 : M.a (t + 1) = 0) (ha0 : M.a t = 0)
    (ha : ∀ i ∈ Finset.Icc 1 t, M.a i = 0 ∨ M.a i = 1) (j : Fin n)
    (hp : ∀ z : ℝ, 0 ≤ z →
      (M.p (t + 1) j : EReal) + TopkisRation.Levels.rightDeriv (M.h (t + 1)) z ≤ (M.p t j : EReal))
    (z₀ z₁ : WithTop ℝ) (hz₀ : TopkisRation.Levels.IsCriticalLevel (M.levelObj t j) z₀)
    (hz₁ : TopkisRation.Levels.IsCriticalLevel (M.levelObj (t + 1) j) z₁) :
    z₀ ≤ z₁ := by
  rw [T2Aux.levelObj_eq] at hz₀ hz₁
  exact T2Aux.main (T2Aux.toL M) (T2Aux.standing M hM) t ht1 htk ha1 ha0 j hp z₀ z₁ hz₀ hz₁
