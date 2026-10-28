-- Prove2me | solution 1 for PartialCompletion.Budget.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T17:13:12.861818+00:00
-- url     : https://prove2.me/submissions/7dae2071-fd73-45fd-b6d4-f6ef63cc3f94

import Mathlib
import Definitions.Def_PartialCompletion_Budget_Model

set_option autoImplicit false

namespace PC31P3

open PartialCompletion.Budget Set

lemma monoIcc {f f' : ℝ → ℝ} {a b : ℝ} (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (h0 : ∀ x ∈ Ioo a b, 0 ≤ f' x) : MonotoneOn f (Icc a b) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx ⊢
      exact (hf x (Ioo_subset_Icc_self hx)).hasDerivWithinAt)
    (fun x hx => by rw [interior_Icc] at hx; exact h0 x hx)

lemma monoIci {f f' : ℝ → ℝ} {a : ℝ} (hf : ∀ x ∈ Ici a, HasDerivAt f (f' x) x)
    (h0 : ∀ x ∈ Ioi a, 0 ≤ f' x) : MonotoneOn f (Ici a) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici a)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => by
      rw [interior_Ici] at hx ⊢
      exact (hf x (Ioi_subset_Ici_self hx)).hasDerivWithinAt)
    (fun x hx => by rw [interior_Ici] at hx; exact h0 x hx)

lemma antiIci {f f' : ℝ → ℝ} {a : ℝ} (hf : ∀ x ∈ Ici a, HasDerivAt f (f' x) x)
    (h0 : ∀ x ∈ Ioi a, f' x ≤ 0) : AntitoneOn f (Ici a) :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => by
      rw [interior_Ici] at hx ⊢
      exact (hf x (Ioi_subset_Ici_self hx)).hasDerivWithinAt)
    (fun x hx => by rw [interior_Ici] at hx; exact h0 x hx)

lemma smonoIci {f f' : ℝ → ℝ} {a : ℝ} (hf : ∀ x ∈ Ici a, HasDerivAt f (f' x) x)
    (h0 : ∀ x ∈ Ioi a, 0 < f' x) : StrictMonoOn f (Ici a) :=
  strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici a)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => by
      rw [interior_Ici] at hx ⊢
      exact (hf x (Ioi_subset_Ici_self hx)).hasDerivWithinAt)
    (fun x hx => by rw [interior_Ici] at hx; exact h0 x hx)

variable {M : Model}

lemma g_cont (hM : M.Standing) : ContinuousOn M.g (Ici 1) :=
  fun x hx => (hM.hasDerivAt_g x hx).continuousAt.continuousWithinAt

lemma g'_mono (hM : M.Standing) : MonotoneOn M.g' (Ici 1) :=
  monoIci (fun x hx => hM.hasDerivAt_g' x hx) (fun x hx => hM.g''_nonneg x (le_of_lt hx))

lemma g_smono (hM : M.Standing) : StrictMonoOn M.g (Ici 1) :=
  smonoIci (fun x hx => hM.hasDerivAt_g x hx) (fun x hx => hM.g'_pos x (le_of_lt hx))

lemma g_le (hM : M.Standing) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : M.g a ≤ M.g b :=
  (g_smono hM).monotoneOn (show a ∈ Ici 1 from ha) (show b ∈ Ici 1 from le_trans ha hab) hab

lemma g_lt (hM : M.Standing) {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) : M.g a < M.g b :=
  g_smono hM (show a ∈ Ici 1 from ha) (show b ∈ Ici 1 from by simp only [mem_Ici]; linarith) hab

lemma g_pos (hM : M.Standing) {n : ℝ} (hn : 1 ≤ n) : 0 < M.g n := by
  have := g_le hM (le_refl 1) hn
  linarith [hM.g_one_pos]

lemma lt_of_g_lt (hM : M.Standing) {a b : ℝ} (hb : 1 ≤ b) (h : M.g a < M.g b) : a < b := by
  by_contra hc
  push Not at hc
  have := g_le hM hb hc
  linarith

lemma g'_le (hM : M.Standing) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : M.g' a ≤ M.g' b :=
  g'_mono hM (show a ∈ Ici 1 from ha) (show b ∈ Ici 1 from le_trans ha hab) hab

noncomputable def hh (M : Model) (n : ℝ) : ℝ := 1 - M.θ / (4 * n) - M.g n

noncomputable def ψ (M : Model) (a : ℝ) : ℝ := effort M a - M.β * effort M a ^ 2

def uu (k t : ℝ) : ℝ := (max (t - k) 0) ^ 2

lemma W_eq (M : Model) (p : ℝ × ℝ) : W M p = p.2 * hh M p.1 + ψ M p.2 := by
  unfold W hh ψ; ring

lemma ψ_eq (hM : M.Standing) (a : ℝ) :
    ψ M a = 1 / (4 * M.β) - M.β * uu (1 - 1 / (2 * M.β)) a := by
  have hb := hM.β_pos
  unfold ψ effort uu
  rcases le_total (1 / (2 * M.β)) (1 - a) with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]
    field_simp; ring
  · rw [min_eq_right h, max_eq_left (by linarith)]
    field_simp; ring

lemma ψ_le (hM : M.Standing) (a : ℝ) : ψ M a ≤ 1 / (4 * M.β) := by
  rw [ψ_eq hM]
  have := hM.β_pos
  have : 0 ≤ uu (1 - 1 / (2 * M.β)) a := by unfold uu; positivity
  nlinarith

lemma ψ_const (hM : M.Standing) {a : ℝ} (ha : a ≤ 1 - 1 / (2 * M.β)) :
    ψ M a = 1 / (4 * M.β) := by
  rw [ψ_eq hM]; unfold uu; rw [max_eq_right (by linarith)]; ring

lemma ψ_cont (M : Model) : Continuous (ψ M) := by
  unfold ψ effort; fun_prop

lemma u_convex (k : ℝ) : ConvexOn ℝ univ (uu k) := by
  have hl : ConvexOn ℝ univ (fun t : ℝ => t - k) :=
    (convexOn_id convex_univ).sub (concaveOn_const k convex_univ)
  have h1 : ConvexOn ℝ univ (fun t : ℝ => max (t - k) 0) :=
    hl.sup (convexOn_const 0 convex_univ)
  exact h1.pow (fun _ _ => le_max_right _ _) 2

lemma u_slope (k : ℝ) {B B' x x' : ℝ} (hB : 0 < B) (hBB : B < B') (hx : 0 ≤ x)
    (hxx : x < x') :
    B' * (uu k (B * x') - uu k (B * x)) ≤ B * (uu k (B' * x') - uu k (B' * x)) := by
  have hc := u_convex k
  have hB' : 0 < B' := lt_trans hB hBB
  have d1 : 0 < B * x' - B * x := by nlinarith
  have d2 : 0 < B' * x' - B' * x := by nlinarith
  have d3 : 0 < B' * x' - B * x := by nlinarith
  have h1 := hc.secant_mono (a := B * x) (x := B * x') (y := B' * x') trivial trivial trivial
    (by intro h; linarith) (by intro h; linarith) (by nlinarith)
  have h2 := hc.secant_mono (a := B' * x') (x := B * x) (y := B' * x) trivial trivial trivial
    (by intro h; linarith) (by intro h; linarith) (by nlinarith)
  have e1 : (uu k (B' * x') - uu k (B * x)) / (B' * x' - B * x) =
      (uu k (B * x) - uu k (B' * x')) / (B * x - B' * x') := by
    rw [div_eq_div_iff (by linarith) (by linarith)]; ring
  have e2 : (uu k (B' * x) - uu k (B' * x')) / (B' * x - B' * x') =
      (uu k (B' * x') - uu k (B' * x)) / (B' * x' - B' * x) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]; ring
  have key : (uu k (B * x') - uu k (B * x)) / (B * x' - B * x) ≤
      (uu k (B' * x') - uu k (B' * x)) / (B' * x' - B' * x) := by
    linarith
  rw [div_le_div_iff₀ d1 d2] at key
  by_contra hcon
  push Not at hcon
  have := mul_pos (sub_pos.2 hxx) (sub_pos.2 hcon)
  nlinarith

lemma ψ_slope (hM : M.Standing) {B B' G G' : ℝ} (hB : 0 < B) (hBB : B < B') (hG : 0 < G')
    (hGG : G' < G) :
    B * (ψ M (B' / G') - ψ M (B' / G)) ≤ B' * (ψ M (B / G') - ψ M (B / G)) := by
  have hG0 : 0 < G := lt_trans hG hGG
  have hs := u_slope (1 - 1 / (2 * M.β)) hB hBB (x := 1 / G) (x' := 1 / G')
    (by positivity) (one_div_lt_one_div_of_lt hG hGG)
  simp only [mul_one_div] at hs
  rw [ψ_eq hM, ψ_eq hM, ψ_eq hM, ψ_eq hM]
  have := hM.β_pos
  nlinarith [mul_le_mul_of_nonneg_left hs this.le]

/-! ### the variety value `hh` -/

lemma inv_deriv {x : ℝ} (θ : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => θ / (4 * y)) (-(θ / (4 * x ^ 2))) x := by
  have h4 : (fun y : ℝ => 4 * id y) x ≠ 0 := by simp [hx]
  exact ((hasDerivAt_const x θ).div ((hasDerivAt_id x).const_mul 4) h4).congr_deriv
    (by simp only [id]; field_simp; ring)

lemma hh_deriv (hM : M.Standing) {x : ℝ} (hx : 1 ≤ x) :
    HasDerivAt (hh M) (M.θ / (4 * x ^ 2) - M.g' x) x := by
  have hx0 : x ≠ 0 := by positivity
  exact (((hasDerivAt_const x (1:ℝ)).sub (inv_deriv M.θ hx0)).sub
    (hM.hasDerivAt_g x hx)).congr_deriv (by ring)

lemma nnb_le {N : ℝ} (hN : IsNNB M N) : M.θ / (4 * N ^ 2) ≤ M.g' N := by
  rcases eq_or_lt_of_le hN.1 with h | h
  · subst h; simpa using hN.2.1 rfl
  · exact (hN.2.2 h).le

lemma hh_mono (hM : M.Standing) {N : ℝ} (hN : IsNNB M N) : MonotoneOn (hh M) (Icc 1 N) :=
  monoIcc (fun x hx => hh_deriv hM hx.1) (fun x hx => by
    have hN1 : 1 < N := lt_trans hx.1 hx.2
    have e := hN.2.2 hN1
    have hg := g'_le hM (le_of_lt hx.1) hx.2.le
    have hxN := hx.2.le
    have h1 := hx.1
    have hθ := hM.θ_pos
    have : M.θ / (4 * N ^ 2) ≤ M.θ / (4 * x ^ 2) := by gcongr
    linarith)

lemma hh_anti (hM : M.Standing) {N : ℝ} (hN : IsNNB M N) : AntitoneOn (hh M) (Ici N) :=
  antiIci (fun x hx => hh_deriv hM (le_trans hN.1 hx)) (fun x hx => by
    have hxN : N ≤ x := le_of_lt hx
    have hg := g'_le hM hN.1 hxN
    have hn1 := hN.1
    have hθ := hM.θ_pos
    have : M.θ / (4 * x ^ 2) ≤ M.θ / (4 * N ^ 2) := by gcongr
    have := nnb_le hN
    linarith)

lemma hh_max (hM : M.Standing) {N : ℝ} (hN : IsNNB M N) {n : ℝ} (hn : 1 ≤ n) :
    hh M n ≤ hh M N := by
  rcases le_total n N with h | h
  · exact hh_mono hM hN ⟨hn, h⟩ ⟨hN.1, le_refl N⟩ h
  · exact hh_anti hM hN (show N ∈ Ici N from le_refl N) (show n ∈ Ici N from h) h

lemma hh_pos (hM : M.Standing) {N : ℝ} (hN : IsNNB M N) : 0 < hh M N := by
  obtain ⟨n, hn, hlt⟩ := hM.worthwhile
  have := hh_max hM hN hn
  unfold hh at this ⊢
  linarith

lemma hh_lt (hM : M.Standing) {N : ℝ} (hN : IsNNB M N) : hh M N < 1 := by
  have := g_pos hM hN.1
  have hθ := hM.θ_pos
  have : 0 < M.θ / (4 * N) := by have := hN.1; positivity
  unfold hh; linarith

/-! ### the completion problem at fixed variety -/

lemma A_eq (N : ℝ) : alphaAmple M N = max (1 - (1 - hh M N) / (2 * M.β)) 0 := by
  unfold alphaAmple hh; congr 2; ring

lemma f_mono_aux {β H s t : ℝ} (hb : 0 < β) (hH : 0 < H) (hs : 0 ≤ s) (hst : s ≤ t)
    (htA : t ≤ max (1 - (1 - H) / (2 * β)) 0) :
    s * H - β * uu (1 - 1 / (2 * β)) s ≤ t * H - β * uu (1 - 1 / (2 * β)) t := by
  unfold uu
  set k := 1 - 1 / (2 * β) with hk
  have hA : 1 - (1 - H) / (2 * β) = k + H / (2 * β) := by rw [hk]; field_simp; ring
  rw [hA] at htA
  rcases le_total t k with htk | htk
  · rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    nlinarith
  · rcases le_total (k + H / (2 * β)) 0 with h0 | h0
    · rw [max_eq_right h0] at htA
      have : s = t := le_antisymm hst (by linarith)
      subst this; exact le_refl _
    · rw [max_eq_left h0] at htA
      set p := max (t - k) 0 with hp
      set q := max (s - k) 0 with hq
      have hpe : p = t - k := max_eq_left (by linarith)
      have hq0 : 0 ≤ q := le_max_right _ _
      have hqs : s - k ≤ q := le_max_left _ _
      have hqp : q ≤ p := max_le (by linarith) (by linarith)
      have hpH : p * (2 * β) ≤ H := by
        have : p ≤ H / (2 * β) := by linarith
        rwa [le_div_iff₀ (by positivity)] at this
      have h2 : (p - q) * (p + q) ≤ (t - s) * (2 * p) :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left h2 hb.le,
        mul_le_mul_of_nonneg_left hpH (sub_nonneg.2 hst)]

lemma f_max_aux {β H t : ℝ} (hb : 0 < β) (hH : 0 < H) (ht : 0 ≤ t) :
    t * H - β * uu (1 - 1 / (2 * β)) t ≤
      max (1 - (1 - H) / (2 * β)) 0 * H - β * uu (1 - 1 / (2 * β)) (max (1 - (1 - H) / (2 * β)) 0) := by
  set A := max (1 - (1 - H) / (2 * β)) 0 with hAdef
  rcases le_total t A with h | h
  · exact f_mono_aux hb hH ht h (le_refl _)
  · unfold uu
    set k := 1 - 1 / (2 * β) with hk
    have hA : 1 - (1 - H) / (2 * β) = k + H / (2 * β) := by rw [hk]; field_simp; ring
    have hAk : k + H / (2 * β) ≤ A := by rw [hAdef, hA]; exact le_max_left _ _
    have hpos : 0 < H / (2 * β) := by positivity
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    have hc : H ≤ β * (2 * (A - k)) := by
      have : H / (2 * β) ≤ A - k := by linarith
      rw [div_le_iff₀ (by positivity)] at this; linarith
    nlinarith [mul_le_mul_of_nonneg_left hc (sub_nonneg.2 h),
      mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 h), hb.le]

lemma A_props (hM : M.Standing) {N : ℝ} (hN : IsNNB M N) :
    0 ≤ alphaAmple M N ∧ alphaAmple M N ≤ 1 ∧ 1 - 1 / (2 * M.β) < alphaAmple M N := by
  have hH := hh_pos hM hN
  have hH1 := hh_lt hM hN
  have hb := hM.β_pos
  rw [A_eq]
  refine ⟨le_max_right _ _, max_le ?_ zero_le_one, ?_⟩
  · have : 0 ≤ (1 - hh M N) / (2 * M.β) := div_nonneg (by linarith) (by positivity)
    linarith
  · have : (1 - hh M N) / (2 * M.β) < 1 / (2 * M.β) :=
      div_lt_div_of_pos_right (by linarith) (by positivity)
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)

/-- the value along fixed optimal variety `N` -/
lemma fN_mono (hM : M.Standing) {N : ℝ} (hN : IsNNB M N) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ alphaAmple M N) :
    s * hh M N + ψ M s ≤ t * hh M N + ψ M t := by
  rw [A_eq] at ht
  rw [ψ_eq hM, ψ_eq hM]
  have := f_mono_aux hM.β_pos (hh_pos hM hN) hs hst ht
  linarith

lemma fN_max (hM : M.Standing) {N : ℝ} (hN : IsNNB M N) {t : ℝ} (ht : 0 ≤ t) :
    t * hh M N + ψ M t ≤ alphaAmple M N * hh M N + ψ M (alphaAmple M N) := by
  rw [A_eq, ψ_eq hM, ψ_eq hM]
  have := f_max_aux hM.β_pos (hh_pos hM hN) ht
  linarith

lemma W_bind (M : Model) {B m : ℝ} (hg : M.g m ≠ 0) :
    W M (m, B / M.g m) = B / M.g m * (1 - M.θ / (4 * m)) - B + ψ M (B / M.g m) := by
  have : B / M.g m * M.g m = B := div_mul_cancel₀ B hg
  rw [W_eq]; unfold hh
  linear_combination (-1 : ℝ) * this

/-! ### reduction to the binding curve -/

lemma reduce (hM : M.Standing) {N : ℝ} (hN : IsNNB M N) {B : ℝ} (hB0 : 0 ≤ B)
    (hB2 : B < alphaAmple M N * M.g N) {p : ℝ × ℝ} (hp : p ∈ Feasible M B) :
    ∃ m, 1 ≤ m ∧ m ≤ N ∧ B ≤ M.g m ∧ W M p ≤ W M (m, B / M.g m) := by
  obtain ⟨n, a⟩ := p
  simp only [Feasible, Unconstrained, mem_ofPred_eq] at hp
  obtain ⟨⟨hn, ha0, ha1⟩, hpB⟩ := hp
  have gN := g_pos hM hN.1
  obtain ⟨hA0, hA1, -⟩ := A_props hM hN
  have hBgN : B ≤ M.g N := by nlinarith
  by_cases hc : a * M.g N ≤ B
  · refine ⟨N, hN.1, le_refl N, hBgN, ?_⟩
    rw [W_eq, W_eq]
    simp only
    have h1 : a * hh M n ≤ a * hh M N := mul_le_mul_of_nonneg_left (hh_max hM hN hn) ha0
    have h2 : a ≤ B / M.g N := by rw [le_div_iff₀ gN]; exact hc
    have h3 : B / M.g N ≤ alphaAmple M N := by rw [div_le_iff₀ gN]; exact hB2.le
    have := fN_mono hM hN ha0 h2 h3
    linarith
  · push Not at hc
    have ha : 0 < a := by
      rcases eq_or_lt_of_le ha0 with h | h
      · subst h; simp at hc; linarith
      · exact h
    have hnN : n < N := by
      by_contra hcon
      push Not at hcon
      have := g_le hM hN.1 hcon
      nlinarith
    have hgn := g_pos hM hn
    have hcont : ContinuousOn M.g (Icc n N) := (g_cont hM).mono (fun x hx => le_trans hn hx.1)
    have hmem : B / a ∈ Icc (M.g n) (M.g N) := by
      constructor
      · rw [le_div_iff₀ ha]; linarith
      · rw [div_le_iff₀ ha]; linarith
    obtain ⟨m, hm, hgm⟩ := intermediate_value_Icc hnN.le hcont hmem
    have hm1 : 1 ≤ m := le_trans hn hm.1
    have hgm0 := g_pos hM hm1
    have hBpos : 0 < B := by
      have : 0 < B / a := hgm ▸ hgm0
      exact (div_pos_iff_of_pos_right ha).1 this
    have hBa : B / M.g m = a := by rw [hgm]; field_simp
    refine ⟨m, hm1, hm.2, ?_, ?_⟩
    · rw [hgm, le_div_iff₀ ha]; nlinarith
    · rw [hBa, W_eq, W_eq]
      simp only
      have := hh_mono hM hN ⟨hn, hnN.le⟩ ⟨hm1, hm.2⟩ hm.1
      nlinarith

/-! ### large budgets -/

lemma regime3 (hM : M.Standing) {N : ℝ} (hN : IsNNB M N) {B : ℝ}
    (hB : alphaAmple M N * M.g N ≤ B) : IsOptimal M B (N, alphaAmple M N) := by
  obtain ⟨hA0, hA1, -⟩ := A_props hM hN
  refine ⟨?_, isMaxOn_iff.2 ?_⟩
  · simp only [Feasible, Unconstrained, mem_ofPred_eq]
    exact ⟨⟨hN.1, hA0, hA1⟩, hB⟩
  · rintro ⟨n, a⟩ hp
    simp only [Feasible, Unconstrained, mem_ofPred_eq] at hp
    obtain ⟨⟨hn, ha0, ha1⟩, hpB⟩ := hp
    rw [W_eq, W_eq]
    simp only
    have h1 : a * hh M n ≤ a * hh M N := mul_le_mul_of_nonneg_left (hh_max hM hN hn) ha0
    have := fN_max hM hN ha0
    linarith

/-! ### small budgets: the ratio `r` and `Λ1` -/

lemma Λ1_deriv (hM : M.Standing) {x : ℝ} (hx : 1 ≤ x) :
    HasDerivAt (Λ1 M) (-(8 * x - 2 * M.θ) * M.g' x - x * (4 * x - M.θ) * M.g'' x) x := by
  have h1 : HasDerivAt (fun y : ℝ => -y * (4 * y - M.θ)) (-(8 * x - M.θ)) x :=
    (((hasDerivAt_id x).neg).mul (((hasDerivAt_id x).const_mul 4).sub_const M.θ)).congr_deriv
      (by simp only [id, Pi.neg_apply]; ring)
  exact ((h1.mul (hM.hasDerivAt_g' x hx)).add ((hM.hasDerivAt_g x hx).const_mul M.θ)).congr_deriv
    (by ring)

lemma Λ1_anti (hM : M.Standing) : AntitoneOn (Λ1 M) (Ici 1) :=
  antiIci (fun x hx => Λ1_deriv hM hx) (fun x hx => by
    have h1 : (1:ℝ) ≤ x := le_of_lt hx
    have hθ := hM.θ_le_two
    have hθ0 := hM.θ_pos
    have hg' := hM.g'_pos x h1
    have hg'' := hM.g''_nonneg x h1
    have a1 : 0 ≤ (8 * x - 2 * M.θ) * M.g' x := mul_nonneg (by linarith) hg'.le
    have a2 : 0 ≤ x * (4 * x - M.θ) * M.g'' x :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) hg''
    linarith)

noncomputable def rr (M : Model) (n : ℝ) : ℝ := (1 - M.θ / (4 * n)) / M.g n

lemma rr_deriv (hM : M.Standing) {x : ℝ} (hx : 1 ≤ x) :
    HasDerivAt (rr M) (Λ1 M x / (4 * x ^ 2 * M.g x ^ 2)) x := by
  have hx0 : x ≠ 0 := by positivity
  have hg := (g_pos hM hx).ne'
  exact (((hasDerivAt_const x (1:ℝ)).sub (inv_deriv M.θ hx0)).div (hM.hasDerivAt_g x hx)
    hg).congr_deriv (by simp only [Pi.sub_apply]; unfold Λ1; field_simp; ring)

lemma exists_n0 (hM : M.Standing) {N : ℝ} (hN : IsNNB M N) :
    ∃ n0, IsN0 M n0 ∧ n0 ≤ N := by
  have hH := hh_pos hM hN
  have hθ := hM.θ_pos
  have hneg : Λ1 M N < 0 := by
    rcases eq_or_lt_of_le hN.1 with h | h
    · subst h
      have e := hN.2.1 rfl
      unfold hh at hH
      unfold Λ1
      have hθ2 := hM.θ_le_two
      nlinarith [mul_le_mul_of_nonneg_left e (show (0:ℝ) ≤ 4 - M.θ by linarith)]
    · have e := hN.2.2 h
      have hN0 : N ≠ 0 := by linarith
      have : Λ1 M N = -M.θ * hh M N := by
        unfold Λ1 hh; rw [← e]; field_simp; ring
      rw [this]; nlinarith
  by_cases h1 : Λ1 M 1 ≤ 0
  · exact ⟨1, ⟨le_refl 1, fun _ => h1, fun h => absurd h (lt_irrefl 1)⟩, hN.1⟩
  · push Not at h1
    have hcont : ContinuousOn (Λ1 M) (Icc 1 N) :=
      fun x hx => (Λ1_deriv hM hx.1).continuousAt.continuousWithinAt
    obtain ⟨n0, hn0, hz⟩ := intermediate_value_Icc' hN.1 hcont
      (show (0:ℝ) ∈ Icc (Λ1 M N) (Λ1 M 1) from ⟨hneg.le, h1.le⟩)
    refine ⟨n0, ⟨hn0.1, fun h => by rw [← h]; exact hz.le, fun _ => hz⟩, hn0.2⟩

lemma rr_le (hM : M.Standing) {n0 : ℝ} (hn0 : IsN0 M n0) {m : ℝ} (hm : 1 ≤ m) :
    rr M m ≤ rr M n0 := by
  have hpos : ∀ x, 1 ≤ x → 0 < 4 * x ^ 2 * M.g x ^ 2 := fun x hx => by
    have := g_pos hM hx; positivity
  rcases le_total m n0 with h | h
  · have hmono : MonotoneOn (rr M) (Icc 1 n0) :=
      monoIcc (fun x hx => rr_deriv hM hx.1) (fun x hx => by
        have h1 : 1 < n0 := lt_trans hx.1 hx.2
        have hz := hn0.2.2 h1
        have := Λ1_anti hM (show x ∈ Ici 1 from le_of_lt hx.1) (show n0 ∈ Ici 1 from hn0.1)
          hx.2.le
        exact div_nonneg (by linarith) (hpos x (le_of_lt hx.1)).le)
    exact hmono ⟨hm, h⟩ ⟨hn0.1, le_refl _⟩ h
  · have hanti : AntitoneOn (rr M) (Ici n0) :=
      antiIci (fun x hx => rr_deriv hM (le_trans hn0.1 hx)) (fun x hx => by
        have hx1 : 1 ≤ x := le_trans hn0.1 (le_of_lt hx)
        have := Λ1_anti hM (show n0 ∈ Ici 1 from hn0.1) (show x ∈ Ici 1 from hx1) (le_of_lt hx)
        have hz : Λ1 M n0 ≤ 0 := by
          rcases eq_or_lt_of_le hn0.1 with e | e
          · rw [← e]; exact hn0.2.1 e.symm
          · exact (hn0.2.2 e).le
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) (hpos x hx1).le)
    exact hanti (mem_Ici.2 (le_refl n0)) (show m ∈ Ici n0 from h) h

lemma regime1 (hM : M.Standing) {N : ℝ} (hN : IsNNB M N) {n0 : ℝ} (hn0 : IsN0 M n0)
    (hn0N : n0 ≤ N) {B : ℝ} (hB0 : 0 ≤ B) (hB1 : B < (1 - 1 / (2 * M.β)) * M.g n0)
    (hB2 : B < alphaAmple M N * M.g N) : IsOptimal M B (n0, B / M.g n0) := by
  have hg0 := g_pos hM hn0.1
  have hb := hM.β_pos
  have hk : 1 - 1 / (2 * M.β) < 1 := by have : 0 < 1 / (2 * M.β) := by positivity
                                        linarith
  have hBg : B ≤ M.g n0 := by nlinarith
  have hαk : B / M.g n0 ≤ 1 - 1 / (2 * M.β) := by rw [div_le_iff₀ hg0]; linarith
  refine ⟨?_, isMaxOn_iff.2 ?_⟩
  · simp only [Feasible, Unconstrained, mem_ofPred_eq]
    refine ⟨⟨hn0.1, div_nonneg hB0 hg0.le, ?_⟩, ?_⟩
    · rw [div_le_one hg0]; exact hBg
    · rw [div_mul_cancel₀ B hg0.ne']
  · intro p hp
    obtain ⟨m, hm1, hmN, hBm, hle⟩ := reduce hM hN hB0 hB2 hp
    have hgm := g_pos hM hm1
    refine le_trans hle ?_
    rw [W_bind M hgm.ne', W_bind M hg0.ne', ψ_const hM hαk]
    have h1 := ψ_le hM (B / M.g m)
    have h2 := mul_le_mul_of_nonneg_left (rr_le hM hn0 hm1) hB0
    unfold rr at h2
    have e1 : B / M.g m * (1 - M.θ / (4 * m)) = B * ((1 - M.θ / (4 * m)) / M.g m) := by ring
    have e2 : B / M.g n0 * (1 - M.θ / (4 * n0)) = B * ((1 - M.θ / (4 * n0)) / M.g n0) := by ring
    rw [e1, e2]
    linarith

/-! ### the middle regime -/

def II (M : Model) (N B : ℝ) : Set ℝ := Icc 1 N ∩ M.g ⁻¹' Ici B

noncomputable def FF (M : Model) (B m : ℝ) : ℝ := W M (m, B / M.g m)

def SS (M : Model) (N B : ℝ) : Set ℝ :=
  {m | m ∈ II M N B ∧ ∀ t ∈ II M N B, FF M B t ≤ FF M B m}

lemma mem_II {N B m : ℝ} : m ∈ II M N B ↔ (1 ≤ m ∧ m ≤ N) ∧ B ≤ M.g m := by
  simp [II]

lemma FF_cont (hM : M.Standing) (N B : ℝ) : ContinuousOn (FF M B) (Icc 1 N) := by
  have hg : ContinuousOn M.g (Icc 1 N) := (g_cont hM).mono (fun x hx => hx.1)
  have hg0 : ∀ x ∈ Icc 1 N, M.g x ≠ 0 := fun x hx => (g_pos hM hx.1).ne'
  have h4 : ∀ x ∈ Icc (1:ℝ) N, 4 * x ≠ 0 := fun x hx => by have := hx.1; positivity
  have ha : ContinuousOn (fun m => B / M.g m) (Icc 1 N) := continuousOn_const.div hg hg0
  have hθ : ContinuousOn (fun m : ℝ => M.θ / (4 * m)) (Icc 1 N) :=
    continuousOn_const.div (continuousOn_const.mul continuousOn_id) h4
  have hexp : ContinuousOn (fun m => B / M.g m * (1 - M.θ / (4 * m)) - B + ψ M (B / M.g m))
      (Icc 1 N) :=
    ((ha.mul (continuousOn_const.sub hθ)).sub continuousOn_const).add
      ((ψ_cont M).comp_continuousOn ha)
  refine hexp.congr (fun x hx => ?_)
  exact W_bind M (hg0 x hx)

lemma SS_spec (hM : M.Standing) {N B : ℝ} (hN : IsNNB M N) (hB2 : B < alphaAmple M N * M.g N) :
    sSup (SS M N B) ∈ SS M N B ∧ BddAbove (SS M N B) := by
  obtain ⟨hA0, hA1, -⟩ := A_props hM hN
  have gN := g_pos hM hN.1
  have hcl : IsClosed (II M N B) :=
    ((g_cont hM).mono (fun x hx => hx.1)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hcomp : IsCompact (II M N B) := isCompact_Icc.of_isClosed_subset hcl inter_subset_left
  have hne : (II M N B).Nonempty := ⟨N, mem_II.2 ⟨⟨hN.1, le_refl _⟩, by nlinarith⟩⟩
  have hFc : ContinuousOn (FF M B) (II M N B) := (FF_cont hM N B).mono inter_subset_left
  obtain ⟨x0, hx0, hmax⟩ := hcomp.exists_isMaxOn hne hFc
  have hS : SS M N B = II M N B ∩ FF M B ⁻¹' Ici (FF M B x0) := by
    ext m
    simp only [SS, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ici]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2 x0 hx0⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun t ht => le_trans (isMaxOn_iff.1 hmax t ht) h2⟩
  have hScl : IsClosed (SS M N B) := by
    rw [hS]; exact hFc.preimage_isClosed_of_isClosed hcl isClosed_Ici
  have hScomp : IsCompact (SS M N B) := hcomp.of_isClosed_subset hScl (by
    intro m hm; exact hm.1)
  have hSne : (SS M N B).Nonempty := ⟨x0, hx0, fun t ht => isMaxOn_iff.1 hmax t ht⟩
  exact ⟨hScomp.sSup_mem hSne, hScomp.bddAbove⟩

lemma topkis (hM : M.Standing) {N B B' m m' : ℝ} (hB : 0 < B) (hBB : B < B')
    (hm : m ∈ SS M N B) (hm' : m' ∈ SS M N B') (hlt : m' < m) : m ∈ SS M N B' := by
  obtain ⟨hmI, hmopt⟩ := hm
  obtain ⟨hm'I, hm'opt⟩ := hm'
  rw [mem_II] at hmI hm'I
  have hm1 := hmI.1.1
  have hm'1 := hm'I.1.1
  have hgl := g_lt hM hm'1 hlt
  have hmI' : m ∈ II M N B' := mem_II.2 ⟨hmI.1, by linarith [hm'I.2]⟩
  have hm'IB : m' ∈ II M N B := mem_II.2 ⟨hm'I.1, by linarith [hm'I.2]⟩
  refine ⟨hmI', fun t ht => le_trans (hm'opt t ht) ?_⟩
  have h0 := hmopt m' hm'IB
  have gm := g_pos hM hm1
  have gm' := g_pos hM hm'1
  unfold FF at h0 ⊢
  rw [W_bind M gm.ne', W_bind M gm'.ne'] at h0 ⊢
  have hs := ψ_slope hM hB hBB gm' hgl
  have hB' : 0 < B' := lt_trans hB hBB
  have key : B' * (B / M.g m * (1 - M.θ / (4 * m)) - B + ψ M (B / M.g m) -
      (B / M.g m' * (1 - M.θ / (4 * m')) - B + ψ M (B / M.g m'))) ≤
      B * (B' / M.g m * (1 - M.θ / (4 * m)) - B' + ψ M (B' / M.g m) -
      (B' / M.g m' * (1 - M.θ / (4 * m')) - B' + ψ M (B' / M.g m'))) := by
    have e1 : B' * (B / M.g m * (1 - M.θ / (4 * m))) = B * (B' / M.g m * (1 - M.θ / (4 * m))) := by
      ring
    have e2 : B' * (B / M.g m' * (1 - M.θ / (4 * m'))) =
        B * (B' / M.g m' * (1 - M.θ / (4 * m'))) := by ring
    nlinarith
  have hpos : 0 ≤ B' * (B / M.g m * (1 - M.θ / (4 * m)) - B + ψ M (B / M.g m) -
      (B / M.g m' * (1 - M.θ / (4 * m')) - B + ψ M (B / M.g m'))) :=
    mul_nonneg hB'.le (by linarith)
  by_contra hcon
  push Not at hcon
  have : B * (B' / M.g m * (1 - M.θ / (4 * m)) - B' + ψ M (B' / M.g m) -
      (B' / M.g m' * (1 - M.θ / (4 * m')) - B' + ψ M (B' / M.g m'))) < 0 :=
    mul_neg_of_pos_of_neg hB (by linarith)
  linarith

/-! ### chord slopes of the curve `n ↦ (g n, -1/n)` -/

lemma cmvt (hM : M.Standing) {s t : ℝ} (hs : 1 ≤ s) (hst : s < t) :
    (1 / s - 1 / t) * (s ^ 2 * M.g' s) ≤ M.g t - M.g s ∧
      M.g t - M.g s ≤ (1 / s - 1 / t) * (t ^ 2 * M.g' t) := by
  have hpos : ∀ y ∈ Icc s t, 1 ≤ y := fun y hy => le_trans hs hy.1
  have hinv : ∀ y : ℝ, 1 ≤ y → HasDerivAt (fun z : ℝ => -z⁻¹) ((y ^ 2)⁻¹) y := fun y hy =>
    (hasDerivAt_inv (by positivity)).neg.congr_deriv (neg_neg _)
  obtain ⟨ξ, hξ, e⟩ := exists_ratio_hasDerivAt_eq_ratio_slope (fun z : ℝ => -z⁻¹)
    (fun y => (y ^ 2)⁻¹) hst
    (fun y hy => (hinv y (hpos y hy)).continuousAt.continuousWithinAt)
    (fun y hy => hinv y (le_trans hs hy.1.le)) M.g M.g'
    (fun y hy => (hM.hasDerivAt_g y (hpos y hy)).continuousAt.continuousWithinAt)
    (fun y hy => hM.hasDerivAt_g y (le_trans hs hy.1.le))
  have hξ1 : 1 ≤ ξ := le_trans hs hξ.1.le
  have hξ0 : ξ ≠ 0 := by positivity
  have e2 : M.g t - M.g s = (1 / s - 1 / t) * (ξ ^ 2 * M.g' ξ) := by
    have : M.g t - M.g s = (M.g t - M.g s) * (ξ ^ 2)⁻¹ * ξ ^ 2 := by field_simp
    rw [this, e]; ring
  have hP : 0 ≤ 1 / s - 1 / t := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le (by linarith) hst.le
  have hw1 : s ^ 2 * M.g' s ≤ ξ ^ 2 * M.g' ξ :=
    mul_le_mul (pow_le_pow_left₀ (by linarith) hξ.1.le 2) (g'_le hM hs hξ.1.le)
      (hM.g'_pos s hs).le (by positivity)
  have hw2 : ξ ^ 2 * M.g' ξ ≤ t ^ 2 * M.g' t :=
    mul_le_mul (pow_le_pow_left₀ (by linarith) hξ.2.le 2) (g'_le hM hξ1 hξ.2.le)
      (hM.g'_pos ξ hξ1).le (by positivity)
  rw [e2]
  exact ⟨mul_le_mul_of_nonneg_left hw1 hP, mul_le_mul_of_nonneg_left hw2 hP⟩

lemma four (hM : M.Standing) {a b c d : ℝ} (ha : 1 ≤ a) (hab : a < b) (hcd : c < d)
    (hac : a < c) (hbd : b < d) :
    (1 / c - 1 / d) * (M.g b - M.g a) ≤ (1 / a - 1 / b) * (M.g d - M.g c) := by
  have hc1 : 1 ≤ c := by linarith
  have hb1 : 1 ≤ b := by linarith
  have Pnn : ∀ s t : ℝ, 1 ≤ s → s ≤ t → 0 ≤ 1 / s - 1 / t := fun s t hs hst => by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le (by linarith) hst
  have wmono : ∀ s t : ℝ, 1 ≤ s → s ≤ t → s ^ 2 * M.g' s ≤ t ^ 2 * M.g' t := fun s t hs hst =>
    mul_le_mul (pow_le_pow_left₀ (by linarith) hst 2) (g'_le hM hs hst)
      (hM.g'_pos s hs).le (by positivity)
  by_cases hbc : b ≤ c
  · obtain ⟨-, h2⟩ := cmvt hM ha hab
    obtain ⟨h3, -⟩ := cmvt hM hc1 hcd
    have hw := wmono b c hb1 hbc
    have hP := Pnn a b ha hab.le
    have hQ := Pnn c d hc1 hcd.le
    nlinarith [mul_le_mul_of_nonneg_left h2 hQ, mul_le_mul_of_nonneg_left hw (mul_nonneg hQ hP),
      mul_le_mul_of_nonneg_left h3 hP]
  · push Not at hbc
    obtain ⟨-, u1⟩ := cmvt hM ha hac
    obtain ⟨l2, u2⟩ := cmvt hM hc1 hbc
    obtain ⟨l3, -⟩ := cmvt hM hb1 hbd
    have Pac := Pnn a c ha hac.le
    have Pcb := Pnn c b hc1 hbc.le
    have Pbd := Pnn b d hb1 hbd.le
    have wcb := wmono c b hc1 hbc.le
    nlinarith [mul_le_mul_of_nonneg_left u1 Pcb, mul_le_mul_of_nonneg_left l2 Pac,
      mul_le_mul_of_nonneg_left u1 Pbd, mul_le_mul_of_nonneg_left wcb (mul_nonneg Pbd Pac),
      mul_le_mul_of_nonneg_left l3 Pac, mul_le_mul_of_nonneg_left u2 Pbd,
      mul_le_mul_of_nonneg_left l3 Pcb]

lemma alpha_mono (hM : M.Standing) {N B B' m m' : ℝ} (hB : 0 < B) (hBB : B < B')
    (hm : m ∈ SS M N B) (hm' : m' ∈ SS M N B') (hmax : ∀ t ∈ SS M N B, t ≤ m)
    (hmm' : m ≤ m') : B / M.g m ≤ B' / M.g m' := by
  obtain ⟨hmI, hmopt⟩ := hm
  obtain ⟨hm'I, hm'opt⟩ := hm'
  have hmI0 := hmI
  rw [mem_II] at hmI hm'I
  have hm1 := hmI.1.1
  have hm'1 := hm'I.1.1
  have hB' : 0 < B' := lt_trans hB hBB
  set G := M.g m with hG
  set G' := M.g m' with hG'
  have gm : 0 < G := g_pos hM hm1
  have gm' : 0 < G' := g_pos hM hm'1
  by_contra hlt
  push Not at hlt
  have hcross : B' * G < B * G' := by
    rw [div_lt_div_iff₀ gm' gm] at hlt; linarith
  have hcont : ContinuousOn M.g (Icc m m') := (g_cont hM).mono (fun x hx => le_trans hm1 hx.1)
  -- the point at budget B with completion B'/G'
  have hT1 : B * G' / B' ∈ Icc (M.g m) (M.g m') := by
    constructor
    · rw [le_div_iff₀ hB']; linarith
    · rw [div_le_iff₀ hB']; nlinarith
  obtain ⟨mt, hmt, hgmt⟩ := intermediate_value_Icc hmm' hcont hT1
  have hT2 : B' * G / B ∈ Icc (M.g m) (M.g m') := by
    constructor
    · rw [le_div_iff₀ hB]; nlinarith
    · rw [div_le_iff₀ hB]; linarith
  obtain ⟨mh, hmh, hgmh⟩ := intermediate_value_Icc hmm' hcont hT2
  have hmt1 : 1 ≤ mt := le_trans hm1 hmt.1
  have hmh1 : 1 ≤ mh := le_trans hm1 hmh.1
  have lt1 : m < mt := lt_of_g_lt hM hmt1 (by
    rw [hgmt, ← hG, lt_div_iff₀ hB']; linarith)
  have lt2 : mt < m' := lt_of_g_lt hM hm'1 (by
    rw [hgmt, ← hG', div_lt_iff₀ hB']; nlinarith)
  have lt3 : m < mh := lt_of_g_lt hM hmh1 (by
    rw [hgmh, ← hG, lt_div_iff₀ hB]; nlinarith)
  have lt4 : mh < m' := lt_of_g_lt hM hm'1 (by
    rw [hgmh, ← hG', div_lt_iff₀ hB]; linarith)
  have hmtI : mt ∈ II M N B := mem_II.2 ⟨⟨hmt1, le_trans hmt.2 hm'I.1.2⟩, by
    rw [hgmt, le_div_iff₀ hB']; nlinarith [hm'I.2]⟩
  have hmhI : mh ∈ II M N B' := mem_II.2 ⟨⟨hmh1, le_trans hmh.2 hm'I.1.2⟩, by
    rw [hgmh, le_div_iff₀ hB]; nlinarith [hmI.2]⟩
  have hopt' := hm'opt mh hmhI
  have hgmt0 : M.g mt ≠ 0 := (g_pos hM hmt1).ne'
  have hgmh0 : M.g mh ≠ 0 := (g_pos hM hmh1).ne'
  have ha1 : B / M.g mt = B' / G' := by rw [hgmt]; field_simp
  have ha2 : B' / M.g mh = B / G := by rw [hgmh]; field_simp
  -- the four-point chord inequality
  have h4 := four hM hm1 lt3 lt2 lt1 lt4
  have hU : M.g mh - M.g m = (B' - B) * G / B := by rw [hgmh, ← hG]; field_simp
  have hV : M.g m' - M.g mt = (B' - B) * G' / B' := by rw [hgmt, ← hG']; field_simp
  rw [hU, hV] at h4
  have key : B' / G' * (1 / mt - 1 / m') ≤ B / G * (1 / m - 1 / mh) := by
    have hD : 0 < B' - B := by linarith
    have e1 : (1 / mt - 1 / m') * ((B' - B) * G / B) * (B / G * (B' / G')) =
        (B' / G' * (1 / mt - 1 / m')) * (B' - B) := by field_simp
    have e2 : (1 / m - 1 / mh) * ((B' - B) * G' / B') * (B / G * (B' / G')) =
        (B / G * (1 / m - 1 / mh)) * (B' - B) := by field_simp
    have hpos : 0 < B / G * (B' / G') := by positivity
    have := mul_le_mul_of_nonneg_right h4 hpos.le
    rw [e1, e2] at this
    exact le_of_mul_le_mul_right this hD
  have hmtS : mt ∈ SS M N B := by
    refine ⟨hmtI, fun t ht => le_trans (hmopt t ht) ?_⟩
    unfold FF at hopt' ⊢
    rw [W_bind M hgmt0, W_bind M gm.ne', ha1]
    rw [W_bind M hgmh0, W_bind M gm'.ne', ha2] at hopt'
    have hd : ∀ x : ℝ, M.θ / (4 * x) = M.θ / 4 * (1 / x) := fun x => by ring
    simp only [hd] at hopt' ⊢
    have := mul_le_mul_of_nonneg_left key (show (0:ℝ) ≤ M.θ / 4 by linarith [hM.θ_pos])
    nlinarith
  have := hmax mt hmtS
  linarith

end PC31P3

open PartialCompletion.Budget PC31P3 in
theorem prop3_main (M : Model) (hM : M.Standing)
    (nNB : ℝ) (hNB : IsNNB M nNB) :
    ∃ B1 n0 : ℝ, ∃ n1 : ℝ → ℝ,
      0 ≤ B1 ∧
      B1 ≤ alphaAmple M nNB * M.g nNB ∧
      IsN0 M n0 ∧
      (1 - 1 / (2 * M.β)) * M.g n0 ≤ B1 ∧
      (∀ B : ℝ, 0 ≤ B → B < B1 →
        IsOptimal M B (n0, B / M.g n0)) ∧
      (∀ B : ℝ, 0 ≤ B → B1 ≤ B →
        B < alphaAmple M nNB * M.g nNB →
        IsOptimal M B (n1 B, B / M.g (n1 B))) ∧
      MonotoneOn n1
        (Set.Ico B1 (alphaAmple M nNB * M.g nNB) ∩ Set.Ici 0) ∧
      MonotoneOn (fun B : ℝ => B / M.g (n1 B))
        (Set.Ico B1 (alphaAmple M nNB * M.g nNB) ∩ Set.Ici 0) ∧
      (∀ B : ℝ, alphaAmple M nNB * M.g nNB ≤ B →
        IsOptimal M B (nNB, alphaAmple M nNB)) := by
  obtain ⟨n0, hn0, hn0N⟩ := exists_n0 hM hNB
  obtain ⟨hA0, hA1, hAk⟩ := A_props hM hNB
  have gN := g_pos hM hNB.1
  have gn0 := g_pos hM hn0.1
  have hgle := g_le hM hn0.1 hn0N
  have hB12 : max 0 ((1 - 1 / (2 * M.β)) * M.g n0) ≤ alphaAmple M nNB * M.g nNB := by
    apply max_le (by positivity)
    rcases le_total (1 - 1 / (2 * M.β)) 0 with h | h
    · nlinarith [mul_nonneg hA0 gN.le, mul_nonneg (neg_nonneg.2 h) gn0.le]
    · nlinarith [mul_le_mul_of_nonneg_left hgle h, mul_le_mul_of_nonneg_right hAk.le gN.le]
  let n1 : ℝ → ℝ := fun B => if 0 < B then sSup (SS M nNB B) else 1
  have n1pos : ∀ B, 0 < B → n1 B = sSup (SS M nNB B) := fun B hB => if_pos hB
  have n1zero : ∀ B, ¬ 0 < B → n1 B = 1 := fun B hB => if_neg hB
  have spec : ∀ B, 0 < B → B < alphaAmple M nNB * M.g nNB →
      n1 B ∈ SS M nNB B ∧ ∀ t ∈ SS M nNB B, t ≤ n1 B := by
    intro B hB hB2
    obtain ⟨h1, h2⟩ := SS_spec hM hNB hB2
    rw [n1pos B hB]
    exact ⟨h1, fun t ht => le_csSup h2 ht⟩
  have n1I : ∀ B, 0 ≤ B → B < alphaAmple M nNB * M.g nNB → 1 ≤ n1 B := by
    intro B hB0 hB2
    by_cases hB : 0 < B
    · have := ((spec B hB hB2).1).1
      rw [mem_II] at this
      exact this.1.1
    · rw [n1zero B hB]
  have hmono1 : MonotoneOn n1
      (Set.Ico (max 0 ((1 - 1 / (2 * M.β)) * M.g n0)) (alphaAmple M nNB * M.g nNB) ∩
        Set.Ici 0) := by
    intro B hB B' hB' hle
    by_cases h0 : 0 < B
    · have h0' : 0 < B' := lt_of_lt_of_le h0 hle
      rcases eq_or_lt_of_le hle with e | hlt
      · rw [e]
      · obtain ⟨hs, -⟩ := spec B h0 hB.1.2
        obtain ⟨hs', hmax'⟩ := spec B' h0' hB'.1.2
        by_contra hcon
        push Not at hcon
        have := hmax' _ (topkis hM h0 hlt hs hs' hcon)
        linarith
    · rw [n1zero B h0]; exact n1I B' hB'.2 hB'.1.2
  refine ⟨max 0 ((1 - 1 / (2 * M.β)) * M.g n0), n0, n1, le_max_left _ _, hB12, hn0,
    le_max_right _ _, ?_, ?_, hmono1, ?_, ?_⟩
  · intro B hB0 hB1
    have hBk : B < (1 - 1 / (2 * M.β)) * M.g n0 := by
      rcases lt_max_iff.1 hB1 with h | h
      · linarith
      · exact h
    exact regime1 hM hNB hn0 hn0N hB0 hBk (lt_of_lt_of_le hB1 hB12)
  · intro B hB0 hB1 hB2
    by_cases hB : 0 < B
    · obtain ⟨⟨hI, hopt⟩, -⟩ := spec B hB hB2
      rw [mem_II] at hI
      have g1 := g_pos hM hI.1.1
      refine ⟨?_, isMaxOn_iff.2 ?_⟩
      · simp only [Feasible, Unconstrained, Set.mem_ofPred_eq]
        exact ⟨⟨hI.1.1, div_nonneg hB0 g1.le, (div_le_one g1).2 hI.2⟩,
          (div_mul_cancel₀ B g1.ne').le⟩
      · intro p hp
        obtain ⟨m, hm1, hmN, hBm, hle⟩ := reduce hM hNB hB0 hB2 hp
        exact le_trans hle (hopt m (mem_II.2 ⟨⟨hm1, hmN⟩, hBm⟩))
    · obtain rfl : B = 0 := le_antisymm (not_lt.1 hB) hB0
      rw [n1zero 0 hB]
      refine ⟨?_, isMaxOn_iff.2 ?_⟩
      · simp only [Feasible, Unconstrained, Set.mem_ofPred_eq]
        simp
      · intro p hp
        obtain ⟨m, -, -, -, hle⟩ := reduce hM hNB le_rfl hB2 hp
        refine le_trans hle ?_
        rw [W_eq, W_eq]
        simp
  · intro B hB B' hB' hle
    show B / M.g (n1 B) ≤ B' / M.g (n1 B')
    by_cases h0 : 0 < B
    · rcases eq_or_lt_of_le hle with e | hlt
      · rw [e]
      · have h0' : 0 < B' := lt_trans h0 hlt
        obtain ⟨hs, hmax⟩ := spec B h0 hB.1.2
        obtain ⟨hs', -⟩ := spec B' h0' hB'.1.2
        exact alpha_mono hM h0 hlt hs hs' hmax (hmono1 hB hB' hle)
    · have : B = 0 := le_antisymm (not_lt.1 h0) hB.2
      rw [this, zero_div]
      exact div_nonneg hB'.2 (g_pos hM (n1I B' hB'.2 hB'.1.2)).le
  · intro B hB
    exact regime3 hM hNB hB

open PartialCompletion.Budget in
theorem solution (M : Model) (hM : M.Standing)
    (nNB : ℝ) (hNB : IsNNB M nNB) :
    ∃ B1 n0 : ℝ, ∃ n1 : ℝ → ℝ,
      0 ≤ B1 ∧
      B1 ≤ alphaAmple M nNB * M.g nNB ∧
      IsN0 M n0 ∧
      (1 - 1 / (2 * M.β)) * M.g n0 ≤ B1 ∧
      (∀ B : ℝ, 0 ≤ B → B < B1 →
        IsOptimal M B (n0, B / M.g n0)) ∧
      (∀ B : ℝ, 0 ≤ B → B1 ≤ B →
        B < alphaAmple M nNB * M.g nNB →
        IsOptimal M B (n1 B, B / M.g (n1 B))) ∧
      MonotoneOn n1
        (Set.Ico B1 (alphaAmple M nNB * M.g nNB) ∩ Set.Ici 0) ∧
      MonotoneOn (fun B : ℝ => B / M.g (n1 B))
        (Set.Ico B1 (alphaAmple M nNB * M.g nNB) ∩ Set.Ici 0) ∧
      (∀ B : ℝ, alphaAmple M nNB * M.g nNB ≤ B →
        IsOptimal M B (nNB, alphaAmple M nNB)) := by
  exact prop3_main M hM nNB hNB
