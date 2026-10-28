-- Prove2me | solution 1 for PerishablePricing.Bounds.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T07:26:23.902+00:00
-- url     : https://prove2.me/submissions/5d8c5e95-127e-458e-9394-eb7f4bd6ead3

import Mathlib
import Definitions.Def_PerishablePricing_Bounds_Myopic

set_option autoImplicit false

namespace PerishablePricing.Bounds.Thm3Red

open MeasureTheory PerishablePricing.Bounds

/-! Abstract bracketing lemmas (no model). -/

theorem upper_abstract (Gf Pi : ℝ → ℝ) (l Sbar S : ℝ)
    (hPi : ConcaveOn ℝ (Set.Ici 0) Pi)
    (hC1 : AntitoneOn (fun x => Gf x - Pi x) (Set.Ici l))
    (hS : IsLargestMaxOn Gf (Set.Ici l) S) (hSbar : IsLargestMaxOn Pi (Set.Ici 0) Sbar) :
    S ≤ max Sbar l := by
  by_contra h
  push Not at h
  set m := max Sbar l with hm
  have hSl : l ≤ S := hS.1.1
  have hSb0 : (0:ℝ) ≤ Sbar := hSbar.1.1
  have hmS : Sbar ≤ m := le_max_left _ _
  have hlm : l ≤ m := le_max_right _ _
  have hS0 : (0:ℝ) ≤ S := by linarith
  have hPiS : Pi S < Pi Sbar := by
    by_contra hc
    push Not at hc
    have : S ∈ argmaxOn Pi (Set.Ici 0) :=
      ⟨hS0, fun y hy => (hSbar.1.2 y hy).trans hc⟩
    have := hSbar.2 this
    linarith
  have hPim : Pi S < Pi m := by
    rcases eq_or_lt_of_le hmS with he | hlt
    · rw [← he]; exact hPiS
    · by_contra hc
      push Not at hc
      have hseg : m ∈ openSegment ℝ S Sbar := by
        rw [openSegment_eq_Ioo' (by linarith : S ≠ Sbar)]
        constructor
        · rw [min_eq_right (by linarith : Sbar ≤ S)]; exact hlt
        · rw [max_eq_left (by linarith : Sbar ≤ S)]; exact h
      have := hPi.left_lt_of_lt_right (x := S) (y := Sbar) (z := m) (Set.mem_Ici.2 hS0)
        (Set.mem_Ici.2 hSb0) hseg (lt_of_le_of_lt hc hPiS)
      linarith
  have h1 := hC1 (Set.mem_Ici.2 hlm) (Set.mem_Ici.2 hSl) h.le
  have h2 := hS.1.2 m (Set.mem_Ici.2 hlm)
  simp only at h1
  linarith

theorem lower_abstract (Gf PiT : ℝ → ℝ) (l Sund S : ℝ)
    (hC2 : MonotoneOn (fun x => Gf x - PiT x) (Set.Icc (max l 0) Sund))
    (hC4 : MonotoneOn Gf (Set.Icc l 0))
    (hS : IsLargestMaxOn Gf (Set.Ici l) S)
    (hSund : IsLargestMaxOn PiT (Set.Ici 0) Sund) :
    max Sund l ≤ S := by
  have hSl : l ≤ S := hS.1.1
  have hS0 : (0:ℝ) ≤ S := by
    by_contra hc
    push Not at hc
    have h1 := hC4 ⟨le_refl S |>.trans' hSl, hc.le⟩ ⟨by linarith, le_refl 0⟩ hc.le
    have : (0:ℝ) ∈ argmaxOn Gf (Set.Ici l) :=
      ⟨Set.mem_Ici.2 (by linarith), fun y hy => (hS.1.2 y hy).trans h1⟩
    have := hS.2 this
    linarith
  rw [max_le_iff]
  refine ⟨?_, hSl⟩
  by_contra hc
  push Not at hc
  have hmx : max l 0 ≤ S := max_le hSl hS0
  have h1 := hC2 ⟨hmx, hc.le⟩ ⟨hmx.trans hc.le, le_rfl⟩ hc.le
  have h2 := hSund.1.2 S (Set.mem_Ici.2 hS0)
  simp only at h1
  have : Sund ∈ argmaxOn Gf (Set.Ici l) :=
    ⟨Set.mem_Ici.2 (by linarith), fun y hy => (hS.1.2 y hy).trans (by linarith)⟩
  have := hS.2 this
  linarith

/-! Model facts about `Π` and `Π̃`. -/

theorem ae_mem (M : Model) (hM : M.Standing) : ∀ᵐ ε ∂M.μ, ε ∈ Set.Icc M.A M.B := by
  have := (measure_eq_zero_iff_ae_notMem).mp hM.support
  filter_upwards [this] with ε hε
  simpa using hε

theorem integrable_of_continuous (M : Model) (hM : M.Standing) {f : ℝ → ℝ}
    (hf : Continuous f) : Integrable f M.μ := by
  haveI := hM.isProbabilityMeasure
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := M.A) (b := M.B)).exists_bound_of_continuousOn
    hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C ((ae_mem M hM).mono fun ε h => hC ε h)

theorem v_continuous (M : Model) (sl d : ℝ) : Continuous fun ε => M.v sl (d + ε) := by
  unfold Model.v
  fun_prop

theorem max_comb_le (a b x y t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    max (a * x + b * y - t) 0 ≤ a * max (x - t) 0 + b * max (y - t) 0 := by
  have h1 := mul_le_mul_of_nonneg_left (le_max_left (x - t) 0) ha
  have h2 := mul_le_mul_of_nonneg_left (le_max_left (y - t) 0) hb
  have h3 := mul_nonneg ha (le_max_right (x - t) 0)
  have h4 := mul_nonneg hb (le_max_right (y - t) 0)
  apply max_le
  · have : a * x + b * y - t = a * (x - t) + b * (y - t) := by
      have : t = a * t + b * t := by rw [← add_mul, hab, one_mul]
      linarith
    linarith
  · linarith

theorem max_comb_le' (a b x y t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    max (t - (a * x + b * y)) 0 ≤ a * max (t - x) 0 + b * max (t - y) 0 := by
  have := max_comb_le a b (-x) (-y) (-t) ha hb hab
  have e1 : a * -x + b * -y - -t = t - (a * x + b * y) := by ring
  have e2 : -x - -t = t - x := by ring
  have e3 : -y - -t = t - y := by ring
  rw [e1, e2, e3] at this
  exact this

theorem v_concave_comb (M : Model) (hM : M.Standing) (a b x y t : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) :
    a * M.v x t + b * M.v y t ≤ M.v (a * x + b * y) t := by
  unfold Model.v
  have h1 := mul_le_mul_of_nonneg_left (max_comb_le a b x y t ha hb hab) hM.hp_nonneg
  have h2 := mul_le_mul_of_nonneg_left (max_comb_le' a b x y t ha hb hab) hM.hm_nonneg
  have e : a * (M.γ * M.c * t) + b * (M.γ * M.c * t) = M.γ * M.c * t := by
    rw [← add_mul, hab, one_mul]
  nlinarith

theorem Pi_concave (M : Model) (hM : M.Standing) (d : ℝ) :
    ConcaveOn ℝ Set.univ (fun sl => M.Pi sl d) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  unfold Model.Pi
  have hix := integrable_of_continuous M hM (v_continuous M x d)
  have hiy := integrable_of_continuous M hM (v_continuous M y d)
  have hiz := integrable_of_continuous M hM (v_continuous M (a * x + b * y) d)
  have hmono : ∫ ε, (a * M.v x (d + ε) + b * M.v y (d + ε)) ∂M.μ
      ≤ ∫ ε, M.v (a * x + b * y) (d + ε) ∂M.μ :=
    integral_mono ((hix.const_mul a).add (hiy.const_mul b)) hiz
      (fun ε => v_concave_comb M hM a b x y (d + ε) ha hb hab)
  rw [integral_add (hix.const_mul a) (hiy.const_mul b), integral_const_mul,
    integral_const_mul] at hmono
  have e : a * (M.P d * d) + b * (M.P d * d) = M.P d * d := by rw [← add_mul, hab, one_mul]
  nlinarith

theorem K_nonneg (M : Model) (hM : M.Standing) (L : ℕ) (hγ : M.γ < 1)
    (hθ : M.hp ≤ (1 - M.γ) * M.θ) : 0 ≤ M.K L := by
  unfold Model.K Model.θt
  have hγ0 := hM.γ_nonneg
  have hθt : 0 ≤ M.θ + M.γ * M.c - M.hp := by
    have := mul_nonneg hγ0 hM.θ_nonneg
    have := mul_nonneg hγ0 hM.c_nonneg
    nlinarith
  apply add_nonneg
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg hγ0 j) hM.hp_nonneg
  · exact mul_nonneg (pow_nonneg hγ0 L) hθt

theorem gap_monotone (M : Model) (hM : M.Standing) (L : ℕ) (hγ : M.γ < 1)
    (hθ : M.hp ≤ (1 - M.γ) * M.θ) (d : ℝ) :
    Monotone (fun sl => M.Pi sl d - M.PiT L sl d) := by
  intro x y hxy
  simp only [Model.PiT]
  have hK := K_nonneg M hM L hγ hθ
  have hix : Integrable (fun ε => max (x - (d + ε)) 0) M.μ :=
    integrable_of_continuous M hM (by fun_prop)
  have hiy : Integrable (fun ε => max (y - (d + ε)) 0) M.μ :=
    integrable_of_continuous M hM (by fun_prop)
  have hI : ∫ ε, max (x - (d + ε)) 0 ∂M.μ ≤ ∫ ε, max (y - (d + ε)) 0 ∂M.μ :=
    integral_mono hix hiy (fun ε => max_le_max (by linarith) le_rfl)
  have h1 := mul_le_mul_of_nonneg_left hI hK
  have h2 := mul_le_mul_of_nonneg_left hxy (mul_nonneg hM.γ_nonneg hM.c_nonneg)
  linarith

/-- The reduction core: Theorem 3 from the three monotonicity facts C1, C2, C4. -/
theorem theorem_3_of_mono (M : Model) (hM : M.Standing) (L : ℕ)
    (hγ : M.γ < 1) (hθ : M.hp ≤ (1 - M.γ) * M.θ) (n : ℕ)
    (s : Fin L → ℝ) (d : ℝ)
    (S Sbar Sund : ℝ)
    (hS : IsLargestMaxOn (fun sl => M.G (M.f n) s sl d) (Set.Ici (sLast s)) S)
    (hSbar : IsLargestMaxOn (fun sl => M.Pi sl d) (Set.Ici 0) Sbar)
    (hSund : IsLargestMaxOn (fun sl => M.PiT L sl d) (Set.Ici 0) Sund)
    (hC1 : AntitoneOn (fun sl => M.G (M.f n) s sl d - M.Pi sl d) (Set.Ici (sLast s)))
    (hC2 : MonotoneOn (fun sl => M.G (M.f n) s sl d - M.PiT L sl d)
      (Set.Icc (max (sLast s) 0) Sund))
    (hC4 : MonotoneOn (fun sl => M.G (M.f n) s sl d) (Set.Icc (sLast s) 0)) :
    max Sund (sLast s) ≤ S ∧ S ≤ max Sbar (sLast s) := by
  refine ⟨lower_abstract _ _ _ Sund S hC2 hC4 hS hSund, ?_⟩
  exact upper_abstract _ (fun sl => M.Pi sl d) _ Sbar S
    ((Pi_concave M hM d).subset (Set.subset_univ _) (convex_Ici 0)) hC1 hS hSbar

/-! Child statements (DECOMPOSE plan) as Props, and the reduction from them. -/

/-- C1: `G_t(s,·,d) − Π_t(·,d)` is antitone on `s_l ≥ s_{l−1}` (upper bound). -/
def C1_stmt : Prop :=
  ∀ (M : Model), M.Standing → ∀ (L : ℕ), 1 ≤ L → (1 - M.γ) * M.c ≤ M.hm → M.γ < 1 →
    M.hp ≤ (1 - M.γ) * M.θ → ∀ (n : ℕ) (s : Fin L → ℝ), s ∈ stateSpace L →
    ∀ d ∈ Set.Icc M.dlo M.dhi,
    AntitoneOn (fun sl => M.G (M.f n) s sl d - M.Pi sl d) (Set.Ici (sLast s))

/-- C2: `G_t(s,·,d) − Π̃_t(·,d)` is monotone on `[s_{l−1} ∨ 0, S̲_t(d)]` (lower bound). -/
def C2_stmt : Prop :=
  ∀ (M : Model), M.Standing → ∀ (L : ℕ), 1 ≤ L → (1 - M.γ) * M.c ≤ M.hm → M.γ < 1 →
    M.hp ≤ (1 - M.γ) * M.θ → ∀ (n : ℕ) (s : Fin L → ℝ), s ∈ stateSpace L →
    ∀ d ∈ Set.Icc M.dlo M.dhi, ∀ Sund : ℝ,
    IsLargestMaxOn (fun sl => M.PiT L sl d) (Set.Ici 0) Sund →
    MonotoneOn (fun sl => M.G (M.f n) s sl d - M.PiT L sl d) (Set.Icc (max (sLast s) 0) Sund)

/-- C4: `G_t(s,·,d)` is monotone on `[s_{l−1}, 0]` (ordering up to a backlog never helps). -/
def C4_stmt : Prop :=
  ∀ (M : Model), M.Standing → ∀ (L : ℕ), 1 ≤ L → (1 - M.γ) * M.c ≤ M.hm → M.γ < 1 →
    M.hp ≤ (1 - M.γ) * M.θ → ∀ (n : ℕ) (s : Fin L → ℝ), s ∈ stateSpace L →
    ∀ d ∈ Set.Icc M.dlo M.dhi,
    MonotoneOn (fun sl => M.G (M.f n) s sl d) (Set.Icc (sLast s) 0)

theorem theorem_3_of_children (h1 : C1_stmt) (h2 : C2_stmt) (h4 : C4_stmt)
    (M : Model) (hM : M.Standing) (L : ℕ) (hL : 1 ≤ L)
    (hback : (1 - M.γ) * M.c ≤ M.hm) (hγ : M.γ < 1) (hθ : M.hp ≤ (1 - M.γ) * M.θ) (n : ℕ)
    (s : Fin L → ℝ) (hs : s ∈ stateSpace L) (d : ℝ) (hd : d ∈ Set.Icc M.dlo M.dhi)
    (S Sbar Sund : ℝ)
    (hS : IsLargestMaxOn (fun sl => M.G (M.f n) s sl d) (Set.Ici (sLast s)) S)
    (hSbar : IsLargestMaxOn (fun sl => M.Pi sl d) (Set.Ici 0) Sbar)
    (hSund : IsLargestMaxOn (fun sl => M.PiT L sl d) (Set.Ici 0) Sund) :
    max Sund (sLast s) ≤ S ∧ S ≤ max Sbar (sLast s) :=
  theorem_3_of_mono M hM L hγ hθ n s d S Sbar Sund hS hSbar hSund
    (h1 M hM L hL hback hγ hθ n s hs d hd) (h2 M hM L hL hback hγ hθ n s hs d hd Sund hSund)
    (h4 M hM L hL hback hγ hθ n s hs d hd)

end PerishablePricing.Bounds.Thm3Red

namespace PerishablePricing.Bounds.Thm3Core

open MeasureTheory PerishablePricing.Bounds

/-! ## Part A: states, the transition `next`, and the reduced depletion value `Hf`. -/

section States

variable {L : ℕ}

def posPart (y : Fin L → ℝ) : Fin L → ℝ := fun i => max (y i) 0

theorem posPart_mem {y : Fin L → ℝ} (hy : y ∈ stateSpace L) : posPart y ∈ stateSpace L :=
  fun _ _ h => max_le_max (hy h) le_rfl

theorem zero_mem : (0 : Fin L → ℝ) ∈ stateSpace L := fun _ _ _ => le_rfl

theorem sLast_eq (s : Fin L → ℝ) (hL : 0 < L) : sLast s = s ⟨L - 1, by omega⟩ := by
  simp [sLast, hL]

theorem sFirst_eq (s : Fin L → ℝ) (hL : 0 < L) : sFirst s = s ⟨0, hL⟩ := by
  simp [sFirst, hL]

theorem le_sLast {s : Fin L → ℝ} (hs : s ∈ stateSpace L) (i : Fin L) : s i ≤ sLast s := by
  have hL : 0 < L := Fin.pos i
  rw [sLast_eq s hL]
  exact hs (Fin.le_iff_val_le_val.2 (by show (i : ℕ) ≤ L - 1; omega))

theorem sFirst_le {s : Fin L → ℝ} (hs : s ∈ stateSpace L) (i : Fin L) : sFirst s ≤ s i := by
  have hL : 0 < L := Fin.pos i
  rw [sFirst_eq s hL]
  exact hs (Fin.le_iff_val_le_val.2 (by show 0 ≤ (i : ℕ); omega))

theorem sFirst_le_sLast {s : Fin L → ℝ} (hs : s ∈ stateSpace L) (hL : 0 < L) :
    sFirst s ≤ sLast s := (sFirst_le hs ⟨0, hL⟩).trans (le_sLast hs _)

theorem sLast_posPart (s : Fin L → ℝ) : sLast (posPart s) = max (sLast s) 0 := by
  unfold sLast posPart; split_ifs <;> simp

theorem sFirst_posPart (s : Fin L → ℝ) : sFirst (posPart s) = max (sFirst s) 0 := by
  unfold sFirst posPart; split_ifs <;> simp

theorem sLast_mono {s s' : Fin L → ℝ} (h : s ≤ s') : sLast s ≤ sLast s' := by
  unfold sLast; split_ifs
  · exact h _
  · exact le_rfl

theorem sFirst_mono {s s' : Fin L → ℝ} (h : s ≤ s') : sFirst s ≤ sFirst s' := by
  unfold sFirst; split_ifs
  · exact h _
  · exact le_rfl

theorem next_apply (s : Fin L → ℝ) (sl a : ℝ) (i : Fin L) :
    next s sl a i = (if h : (i : ℕ) + 1 < L then s ⟨i + 1, h⟩ else sl) - a := by
  unfold next
  split_ifs with h
  · have e : i.succ = Fin.castSucc ⟨i + 1, h⟩ := by ext; simp
    rw [e, Fin.snoc_castSucc]
  · have e : i.succ = Fin.last L := by ext; simp; omega
    rw [e, Fin.snoc_last]

theorem next_mem {s : Fin L → ℝ} (hs : s ∈ stateSpace L) {sl : ℝ} (hsl : sLast s ≤ sl)
    (a : ℝ) : next s sl a ∈ stateSpace L := by
  intro i j hij
  have hij' : (i : ℕ) ≤ j := hij
  rw [next_apply, next_apply]
  apply sub_le_sub_right
  by_cases hj : (j : ℕ) + 1 < L
  · have hi : (i : ℕ) + 1 < L := by omega
    rw [dif_pos hi, dif_pos hj]
    exact hs (Fin.le_iff_val_le_val.2 (by show (i : ℕ) + 1 ≤ (j : ℕ) + 1; omega))
  · rw [dif_neg hj]
    by_cases hi : (i : ℕ) + 1 < L
    · rw [dif_pos hi]; exact (le_sLast hs _).trans hsl
    · rw [dif_neg hi]

theorem next_anti_a (s : Fin L → ℝ) (sl : ℝ) {a a' : ℝ} (h : a ≤ a') :
    next s sl a' ≤ next s sl a := fun i => by
  rw [next_apply, next_apply]; linarith

theorem next_mono_sl (s : Fin L → ℝ) (a : ℝ) {sl sl' : ℝ} (h : sl ≤ sl') :
    next s sl a ≤ next s sl' a := fun i => by
  rw [next_apply, next_apply]
  split_ifs
  · exact le_rfl
  · linarith

theorem next_mono_s {s s' : Fin L → ℝ} (h : s ≤ s') (sl a : ℝ) :
    next s sl a ≤ next s' sl a := fun i => by
  rw [next_apply, next_apply]
  split_ifs with hi
  · linarith [h ⟨(i : ℕ) + 1, hi⟩]
  · exact le_rfl

theorem next_le_zero {s : Fin L → ℝ} (hs : s ∈ stateSpace L) {sl a : ℝ} (hsl : sLast s ≤ sl)
    (ha : sl ≤ a) (i : Fin L) : next s sl a i ≤ 0 := by
  rw [next_apply]
  split_ifs
  · linarith [le_sLast hs ⟨(i : ℕ) + 1, by assumption⟩]
  · linarith

theorem max_sub_max (x a : ℝ) (ha : 0 ≤ a) : max (max x 0 - a) 0 = max (x - a) 0 := by
  rcases le_total x 0 with hx | hx
  · rw [max_eq_right hx, max_eq_right (by linarith : x - a ≤ 0),
      max_eq_right (by linarith : (0 : ℝ) - a ≤ 0)]
  · rw [max_eq_left hx]

theorem posPart_next (s : Fin L → ℝ) {sl a : ℝ} (ha : 0 ≤ a) :
    posPart (next s sl a) = posPart (next (posPart s) sl a) := by
  funext i
  simp only [posPart, next_apply]
  split_ifs
  · exact (max_sub_max _ _ ha).symm
  · rfl

/-- The two invariants of the profit-to-go carried by the induction. -/
structure Inv (F : (Fin L → ℝ) → ℝ) : Prop where
  anti : ∀ x ∈ stateSpace L, ∀ y ∈ stateSpace L, x ≤ y → F y ≤ F x
  pos : ∀ y ∈ stateSpace L, F y = F (posPart y)

theorem Inv.le_zero {F : (Fin L → ℝ) → ℝ} (hF : Inv F) {y : Fin L → ℝ}
    (hy : y ∈ stateSpace L) : F y ≤ F 0 := by
  rw [hF.pos y hy]
  exact hF.anti 0 zero_mem _ (posPart_mem hy) (fun i => le_max_right _ _)

theorem Inv.eq_zero {F : (Fin L → ℝ) → ℝ} (hF : Inv F) {y : Fin L → ℝ}
    (hy : y ∈ stateSpace L) (h0 : ∀ i, y i ≤ 0) : F y = F 0 := by
  rw [hF.pos y hy]
  congr 1
  funext i
  exact max_eq_right (h0 i)

end States

theorem sSup_image_add (f : ℝ → ℝ) (I : Set ℝ) (c : ℝ) (hne : I.Nonempty)
    (hb : BddAbove (f '' I)) :
    sSup ((fun a => c + f a) '' I) = c + sSup (f '' I) := by
  have hne' : (f '' I).Nonempty := hne.image f
  have hb' : BddAbove ((fun a => c + f a) '' I) := by
    obtain ⟨B, hB⟩ := hb
    refine ⟨c + B, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    have := hB (Set.mem_image_of_mem f ha)
    simp only
    linarith
  apply le_antisymm
  · apply csSup_le (hne.image _)
    rintro _ ⟨a, ha, rfl⟩
    have := le_csSup hb (Set.mem_image_of_mem f ha)
    simp only
    linarith
  · have : sSup (f '' I) ≤ sSup ((fun a => c + f a) '' I) - c := by
      apply csSup_le hne'
      rintro _ ⟨a, ha, rfl⟩
      have : c + f a ≤ sSup ((fun a => c + f a) '' I) :=
        le_csSup hb' (Set.mem_image_of_mem (fun a => c + f a) ha)
      linarith
    linarith

section Model

variable {L : ℕ} (M : Model)

theorem θt_nonneg (hM : M.Standing) (hθ : M.hp ≤ (1 - M.γ) * M.θ) : 0 ≤ M.θt := by
  unfold Model.θt
  have := mul_nonneg hM.γ_nonneg hM.θ_nonneg
  have := mul_nonneg hM.γ_nonneg hM.c_nonneg
  nlinarith

/-- `φ − v` on the depletion interval: `−θ̃ (a − t) + γ F(s̃)`. -/
def hfun (F : (Fin L → ℝ) → ℝ) (s : Fin L → ℝ) (sl t a : ℝ) : ℝ :=
  -M.θt * (a - t) + M.γ * F (next s sl a)

/-- The depletion interval `[s₁ ∨ t, s_l ∨ t]`. -/
def Ival (s : Fin L → ℝ) (sl t : ℝ) : Set ℝ := Set.Icc (max (sFirst s) t) (max sl t)

/-- `H(s_l, t) = g − v`: the reduced depletion value. -/
noncomputable def Hf (F : (Fin L → ℝ) → ℝ) (s : Fin L → ℝ) (sl t : ℝ) : ℝ :=
  sSup ((fun a => hfun M F s sl t a) '' Ival s sl t)

theorem phi_eq (F : (Fin L → ℝ) → ℝ) (s : Fin L → ℝ) (sl d ε a : ℝ)
    (ha : a ∈ Ival s sl (d + ε)) :
    M.phi F s sl d a ε = M.v sl (d + ε) + hfun M F s sl (d + ε) a := by
  obtain ⟨h1, h2⟩ := ha
  have hta : d + ε ≤ a := le_trans (le_max_right _ _) h1
  unfold Model.phi Model.v hfun Model.θt
  by_cases has : a ≤ sl
  · rw [max_eq_left (by linarith : 0 ≤ sl - a), max_eq_right (by linarith : a - sl ≤ 0),
      max_eq_left (by linarith : 0 ≤ sl - (d + ε)), max_eq_right (by linarith : d + ε - sl ≤ 0)]
    ring
  · push Not at has
    have hat : a ≤ d + ε := by
      by_contra hc
      push Not at hc
      have : max sl (d + ε) < a := max_lt has hc
      linarith
    have hae : a = d + ε := le_antisymm hat hta
    subst hae
    rw [max_eq_right (by linarith : sl - (d + ε) ≤ 0), max_eq_left (by linarith : 0 ≤ d + ε - sl)]
    ring

variable {M}

theorem Ival_nonempty {s : Fin L → ℝ} (hs : s ∈ stateSpace L) (hL : 0 < L) {sl : ℝ}
    (hsl : sLast s ≤ sl) (t : ℝ) : (Ival s sl t).Nonempty :=
  ⟨max (sFirst s) t, le_rfl, max_le_max ((sFirst_le_sLast hs hL).trans hsl) le_rfl⟩

theorem hfun_le (hM : M.Standing) (hθ : M.hp ≤ (1 - M.γ) * M.θ) {F : (Fin L → ℝ) → ℝ}
    (hF : Inv F) {s : Fin L → ℝ} (hs : s ∈ stateSpace L) {sl : ℝ} (hsl : sLast s ≤ sl)
    {t a : ℝ} (ha : a ∈ Ival s sl t) : hfun M F s sl t a ≤ M.γ * F 0 := by
  have hta : t ≤ a := le_trans (le_max_right _ _) ha.1
  have h1 := mul_nonneg (θt_nonneg M hM hθ) (sub_nonneg.2 hta)
  have h2 := mul_le_mul_of_nonneg_left (hF.le_zero (next_mem hs hsl a)) hM.γ_nonneg
  unfold hfun
  linarith

theorem bdd_hfun (hM : M.Standing) (hθ : M.hp ≤ (1 - M.γ) * M.θ) {F : (Fin L → ℝ) → ℝ}
    (hF : Inv F) {s : Fin L → ℝ} (hs : s ∈ stateSpace L) {sl : ℝ} (hsl : sLast s ≤ sl)
    (t : ℝ) : BddAbove ((fun a => hfun M F s sl t a) '' Ival s sl t) :=
  ⟨M.γ * F 0, by rintro _ ⟨a, ha, rfl⟩; exact hfun_le hM hθ hF hs hsl ha⟩

theorem g_eq (hM : M.Standing) (hθ : M.hp ≤ (1 - M.γ) * M.θ) {F : (Fin L → ℝ) → ℝ}
    (hF : Inv F) {s : Fin L → ℝ} (hs : s ∈ stateSpace L) (hL : 0 < L) {sl : ℝ}
    (hsl : sLast s ≤ sl) (d ε : ℝ) :
    M.g F s sl d ε = M.v sl (d + ε) + Hf M F s sl (d + ε) := by
  unfold Model.g Hf
  have e : (fun a => M.phi F s sl d a ε) '' Set.Icc (max (sFirst s) (d + ε)) (max sl (d + ε))
      = (fun a => M.v sl (d + ε) + hfun M F s sl (d + ε) a) '' Ival s sl (d + ε) :=
    Set.image_congr (fun a ha => phi_eq M F s sl d ε a ha)
  rw [e]
  exact sSup_image_add _ _ _ (Ival_nonempty hs hL hsl _) (bdd_hfun hM hθ hF hs hsl _)

theorem Hf_le (hM : M.Standing) (hθ : M.hp ≤ (1 - M.γ) * M.θ) {F : (Fin L → ℝ) → ℝ}
    (hF : Inv F) {s : Fin L → ℝ} (hs : s ∈ stateSpace L) (hL : 0 < L) {sl : ℝ}
    (hsl : sLast s ≤ sl) (t : ℝ) : Hf M F s sl t ≤ M.γ * F 0 :=
  csSup_le ((Ival_nonempty hs hL hsl t).image _)
    (by rintro _ ⟨a, ha, rfl⟩; exact hfun_le hM hθ hF hs hsl ha)

theorem le_Hf (hM : M.Standing) (hθ : M.hp ≤ (1 - M.γ) * M.θ) {F : (Fin L → ℝ) → ℝ}
    (hF : Inv F) {s : Fin L → ℝ} (hs : s ∈ stateSpace L) {sl : ℝ}
    (hsl : sLast s ≤ sl) {t a : ℝ} (ha : a ∈ Ival s sl t) : hfun M F s sl t a ≤ Hf M F s sl t :=
  le_csSup (bdd_hfun hM hθ hF hs hsl t) (Set.mem_image_of_mem _ ha)

/-- C1 pointwise: `H(·, t)` is antitone on `s_l ≥ s_{l−1}`. -/
theorem Hf_anti_sl (hM : M.Standing) (hθ : M.hp ≤ (1 - M.γ) * M.θ) {F : (Fin L → ℝ) → ℝ}
    (hF : Inv F) {s : Fin L → ℝ} (hs : s ∈ stateSpace L) (hL : 0 < L) {sl sl' : ℝ}
    (hsl : sLast s ≤ sl) (hll : sl ≤ sl') (t : ℝ) : Hf M F s sl' t ≤ Hf M F s sl t := by
  apply csSup_le ((Ival_nonempty hs hL (hsl.trans hll) t).image _)
  rintro _ ⟨a', ha', rfl⟩
  have hγ0 := hM.γ_nonneg
  by_cases hcase : a' ≤ max sl t
  · have ha : a' ∈ Ival s sl t := ⟨ha'.1, hcase⟩
    refine le_trans ?_ (le_Hf hM hθ hF hs hsl ha)
    have h1 := hF.anti _ (next_mem hs hsl a') _ (next_mem hs (hsl.trans hll) a')
      (next_mono_sl s a' hll)
    have h2 := mul_le_mul_of_nonneg_left h1 hγ0
    unfold hfun
    linarith
  · push Not at hcase
    have ha : max sl t ∈ Ival s sl t :=
      ⟨max_le_max ((sFirst_le_sLast hs hL).trans hsl) le_rfl, le_rfl⟩
    refine le_trans ?_ (le_Hf hM hθ hF hs hsl ha)
    have e := hF.eq_zero (next_mem hs hsl (max sl t)) (next_le_zero hs hsl (le_max_left sl t))
    have h1 := mul_le_mul_of_nonneg_left (hF.le_zero (next_mem hs (hsl.trans hll) a')) hγ0
    have h2 := mul_le_mul_of_nonneg_left hcase.le (θt_nonneg M hM hθ)
    unfold hfun
    rw [e]
    linarith

/-- C4 pointwise: for `s_l ≤ 0 ≤ t`, `H(s_l, t) = γ F 0`. -/
theorem Hf_neg (hM : M.Standing) {F : (Fin L → ℝ) → ℝ}
    (hF : Inv F) {s : Fin L → ℝ} (hs : s ∈ stateSpace L) (hL : 0 < L) {sl t : ℝ}
    (hsl : sLast s ≤ sl) (hsl0 : sl ≤ 0) (ht : 0 ≤ t) : Hf M F s sl t = M.γ * F 0 := by
  have hI : Ival s sl t = {t} := by
    unfold Ival
    rw [max_eq_right (by linarith [sFirst_le_sLast hs hL] : sFirst s ≤ t),
      max_eq_right (by linarith : sl ≤ t), Set.Icc_self]
  unfold Hf
  rw [hI, Set.image_singleton, csSup_singleton]
  unfold hfun
  rw [hF.eq_zero (next_mem hs hsl t) (next_le_zero hs hsl (by linarith))]
  ring

/-- Antitonicity of `H` in the state. -/
theorem Hf_anti_s (hM : M.Standing) (hθ : M.hp ≤ (1 - M.γ) * M.θ) {F : (Fin L → ℝ) → ℝ}
    (hF : Inv F) {s s' : Fin L → ℝ} (hs : s ∈ stateSpace L) (hs' : s' ∈ stateSpace L)
    (hL : 0 < L) (hle : s ≤ s') {sl : ℝ} (hsl : sLast s' ≤ sl) (t : ℝ) :
    Hf M F s' sl t ≤ Hf M F s sl t := by
  have hsl0 : sLast s ≤ sl := (sLast_mono hle).trans hsl
  apply csSup_le ((Ival_nonempty hs' hL hsl t).image _)
  rintro _ ⟨a, ha, rfl⟩
  have ha' : a ∈ Ival s sl t := ⟨le_trans (max_le_max (sFirst_mono hle) le_rfl) ha.1, ha.2⟩
  refine le_trans ?_ (le_Hf hM hθ hF hs hsl0 ha')
  have h1 := hF.anti _ (next_mem hs hsl0 a) _ (next_mem hs' hsl a) (next_mono_s hle sl a)
  have h2 := mul_le_mul_of_nonneg_left h1 hM.γ_nonneg
  unfold hfun
  linarith

/-- `H` only sees the positive part of the state when `s_l, t ≥ 0`. -/
theorem Hf_posPart {F : (Fin L → ℝ) → ℝ}
    (hF : Inv F) {s : Fin L → ℝ} (hs : s ∈ stateSpace L) {sl t : ℝ}
    (hsl : sLast s ≤ sl) (hsl0 : 0 ≤ sl) (ht : 0 ≤ t) :
    Hf M F s sl t = Hf M F (posPart s) sl t := by
  have hI : Ival s sl t = Ival (posPart s) sl t := by
    unfold Ival
    rw [sFirst_posPart]
    congr 1
    rcases le_total (sFirst s) 0 with h | h
    · rw [max_eq_right h, max_eq_right ht, max_eq_right (by linarith : sFirst s ≤ t)]
    · rw [max_eq_left h]
  have hsl' : sLast (posPart s) ≤ sl := by rw [sLast_posPart]; exact max_le hsl hsl0
  unfold Hf
  rw [hI]
  congr 1
  apply Set.image_congr
  intro a ha
  have hta : 0 ≤ a := le_trans ht (le_trans (le_max_right _ _) ha.1)
  unfold hfun
  rw [hF.pos _ (next_mem hs hsl a), hF.pos _ (next_mem (posPart_mem hs) hsl' a),
    posPart_next s hta]

end Model

/-! ## Part B: measurability, integrability, `G = Π + ∫ H`, C1 and C4, and the induction. -/

section PartB

variable {L : ℕ} {M : Model}

theorem ae_mem (hM : M.Standing) : ∀ᵐ ε ∂M.μ, ε ∈ Set.Icc M.A M.B := by
  have := (measure_eq_zero_iff_ae_notMem).mp hM.support
  filter_upwards [this] with ε hε
  simpa using hε

theorem ae_t_nonneg (hM : M.Standing) {d : ℝ} (hd : M.dlo ≤ d) : ∀ᵐ ε ∂M.μ, 0 ≤ d + ε :=
  (ae_mem hM).mono fun ε h => by linarith [h.1, hM.demand_nonneg]

theorem integrable_of_continuous (hM : M.Standing) {f : ℝ → ℝ}
    (hf : Continuous f) : Integrable f M.μ := by
  have := hM.isProbabilityMeasure
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := M.A) (b := M.B)).exists_bound_of_continuousOn
    hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C ((ae_mem hM).mono fun ε h => hC ε h)

theorem integrable_of_bounds (hM : M.Standing) {f : ℝ → ℝ} (hf : Measurable f) (lo hi : ℝ)
    (h : ∀ ε ∈ Set.Icc M.A M.B, lo ≤ f ε ∧ f ε ≤ hi) : Integrable f M.μ := by
  have := hM.isProbabilityMeasure
  refine Integrable.of_bound hf.aestronglyMeasurable (|lo| + |hi|) ((ae_mem hM).mono ?_)
  intro ε hε
  obtain ⟨h1, h2⟩ := h ε hε
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [abs_nonneg lo, abs_nonneg hi, neg_abs_le lo, le_abs_self hi]

theorem v_continuous (M : Model) (sl d : ℝ) : Continuous fun ε => M.v sl (d + ε) := by
  unfold Model.v
  fun_prop

theorem v_nonpos (hM : M.Standing) (hback : (1 - M.γ) * M.c ≤ M.hm) {sl t : ℝ} (ht : 0 ≤ t) :
    M.v sl t ≤ 0 := by
  unfold Model.v
  have h1c : 0 ≤ (1 - M.γ) * M.c := mul_nonneg (by linarith [hM.γ_le_one]) hM.c_nonneg
  have hgc : 0 ≤ M.γ * M.c := mul_nonneg hM.γ_nonneg hM.c_nonneg
  rcases le_total t sl with h | h
  · rw [max_eq_left (by linarith : 0 ≤ sl - t), max_eq_right (by linarith : t - sl ≤ 0)]
    have := mul_nonneg h1c (le_trans ht h)
    have := mul_nonneg hgc ht
    have := mul_nonneg hM.hp_nonneg (sub_nonneg.2 h)
    nlinarith
  · rw [max_eq_right (by linarith : sl - t ≤ 0), max_eq_left (by linarith : 0 ≤ t - sl)]
    have := mul_le_mul_of_nonneg_left h (sub_nonneg.2 hback)
    have := mul_nonneg hM.c_nonneg ht
    nlinarith

theorem v_mono_neg (hback : (1 - M.γ) * M.c ≤ M.hm) {sl sl' t : ℝ} (hle : sl ≤ sl')
    (ht : sl' ≤ t) : M.v sl t ≤ M.v sl' t := by
  unfold Model.v
  rw [max_eq_right (by linarith : sl - t ≤ 0), max_eq_left (by linarith : 0 ≤ t - sl),
    max_eq_right (by linarith : sl' - t ≤ 0), max_eq_left (by linarith : 0 ≤ t - sl')]
  have := mul_le_mul_of_nonneg_left (sub_nonneg.2 hle) (sub_nonneg.2 hback)
  nlinarith

theorem Hf_measurable (hM : M.Standing) (hθ : M.hp ≤ (1 - M.γ) * M.θ) {F : (Fin L → ℝ) → ℝ}
    (hF : Inv F) {s : Fin L → ℝ} (hs : s ∈ stateSpace L) (hL : 0 < L) {sl : ℝ}
    (hsl : sLast s ≤ sl) : Measurable fun t => Hf M F s sl t := by
  have hs1 : sFirst s ≤ sl := (sFirst_le_sLast hs hL).trans hsl
  have hθ0 := θt_nonneg M hM hθ
  set ψ : ℝ → ℝ := fun a => -M.θt * a + M.γ * F (next s sl a) with hψ
  set W : ℝ → ℝ := fun t => sSup (ψ '' Set.Icc (min (max (sFirst s) t) sl) sl) with hW
  have hψb : ∀ t, BddAbove (ψ '' Set.Icc (min (max (sFirst s) t) sl) sl) := by
    intro t
    refine ⟨-M.θt * sFirst s + M.γ * F 0, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    have h1 : sFirst s ≤ a := le_trans (le_min (le_max_left _ _) hs1) ha.1
    have h2 := mul_le_mul_of_nonneg_left h1 hθ0
    have h3 := mul_le_mul_of_nonneg_left (hF.le_zero (next_mem hs hsl a)) hM.γ_nonneg
    simp only [hψ]
    linarith
  have hWanti : Antitone W := by
    intro t t' htt
    apply csSup_le_csSup (hψb t) ((Set.nonempty_Icc.2 (min_le_right _ _)).image ψ)
    exact Set.image_mono (Set.Icc_subset_Icc (min_le_min (max_le_max le_rfl htt) le_rfl) le_rfl)
  have hmono : Monotone fun t => M.γ * F (next s sl t) := by
    intro t t' htt
    exact mul_le_mul_of_nonneg_left
      (hF.anti _ (next_mem hs hsl t') _ (next_mem hs hsl t) (next_anti_a s sl htt)) hM.γ_nonneg
  have heq : (fun t => Hf M F s sl t) =
      fun t => if sl ≤ t then M.γ * F (next s sl t) else M.θt * t + W t := by
    funext t
    split_ifs with h
    · have hI : Ival s sl t = {t} := by
        unfold Ival
        rw [max_eq_right (by linarith : sFirst s ≤ t), max_eq_right h, Set.Icc_self]
      unfold Hf
      rw [hI, Set.image_singleton, csSup_singleton]
      unfold hfun
      ring
    · push Not at h
      have hm : min (max (sFirst s) t) sl = max (sFirst s) t := min_eq_left (max_le hs1 h.le)
      have hI : Ival s sl t = Set.Icc (max (sFirst s) t) sl := by
        unfold Ival; rw [max_eq_left h.le]
      unfold Hf
      simp only [hW, hm]
      rw [hI]
      have e : (fun a => hfun M F s sl t a) = fun a => M.θt * t + ψ a := by
        funext a; simp only [hψ, hfun]; ring
      rw [e]
      have hb := hψb t
      rw [hm] at hb
      exact sSup_image_add ψ _ _ (Set.nonempty_Icc.2 (max_le hs1 h.le)) hb
  rw [heq]
  exact Measurable.ite measurableSet_Ici hmono.measurable
    ((measurable_const.mul measurable_id).add hWanti.measurable)

theorem Hf_integrable (hM : M.Standing) (hθ : M.hp ≤ (1 - M.γ) * M.θ) {F : (Fin L → ℝ) → ℝ}
    (hF : Inv F) {s : Fin L → ℝ} (hs : s ∈ stateSpace L) (hL : 0 < L) {sl : ℝ}
    (hsl : sLast s ≤ sl) (d : ℝ) : Integrable (fun ε => Hf M F s sl (d + ε)) M.μ := by
  have hθ0 := θt_nonneg M hM hθ
  refine integrable_of_bounds hM ((Hf_measurable hM hθ hF hs hL hsl).comp
    (measurable_const_add d))
    (-M.θt * max (sFirst s - (d + M.A)) 0 + M.γ * F (next s sl (sFirst s))) (M.γ * F 0) ?_
  intro ε hε
  refine ⟨?_, Hf_le hM hθ hF hs hL hsl _⟩
  have ha : max (sFirst s) (d + ε) ∈ Ival s sl (d + ε) :=
    ⟨le_rfl, max_le_max ((sFirst_le_sLast hs hL).trans hsl) le_rfl⟩
  refine le_trans ?_ (le_Hf hM hθ hF hs hsl ha)
  unfold hfun
  have h1 : max (sFirst s) (d + ε) - (d + ε) ≤ max (sFirst s - (d + M.A)) 0 := by
    rcases le_total (sFirst s) (d + ε) with h | h
    · rw [max_eq_right h]; simp
    · rw [max_eq_left h]; exact le_max_of_le_left (by linarith [hε.1])
  have h2 := mul_le_mul_of_nonneg_left h1 hθ0
  have h3 := hF.anti _ (next_mem hs hsl _) _ (next_mem hs hsl _)
    (next_anti_a s sl (le_max_left (sFirst s) (d + ε)))
  have h4 := mul_le_mul_of_nonneg_left h3 hM.γ_nonneg
  linarith

theorem G_eq (hM : M.Standing) (hθ : M.hp ≤ (1 - M.γ) * M.θ) {F : (Fin L → ℝ) → ℝ}
    (hF : Inv F) {s : Fin L → ℝ} (hs : s ∈ stateSpace L) (hL : 0 < L) {sl : ℝ}
    (hsl : sLast s ≤ sl) (d : ℝ) :
    M.G F s sl d = M.Pi sl d + ∫ ε, Hf M F s sl (d + ε) ∂M.μ := by
  unfold Model.G Model.Pi
  have e : (fun ε => M.g F s sl d ε) = fun ε => M.v sl (d + ε) + Hf M F s sl (d + ε) :=
    funext fun ε => g_eq hM hθ hF hs hL hsl d ε
  rw [e, integral_add (integrable_of_continuous hM (v_continuous M sl d))
    (Hf_integrable hM hθ hF hs hL hsl d)]
  ring

theorem C1_of_inv (hM : M.Standing) (hθ : M.hp ≤ (1 - M.γ) * M.θ) {F : (Fin L → ℝ) → ℝ}
    (hF : Inv F) {s : Fin L → ℝ} (hs : s ∈ stateSpace L) (hL : 0 < L) (d : ℝ) :
    AntitoneOn (fun sl => M.G F s sl d - M.Pi sl d) (Set.Ici (sLast s)) := by
  intro sl hsl sl' hsl' hle
  simp only
  rw [G_eq hM hθ hF hs hL hsl, G_eq hM hθ hF hs hL hsl']
  have := integral_mono (Hf_integrable hM hθ hF hs hL hsl' d)
    (Hf_integrable hM hθ hF hs hL hsl d)
    (fun ε => Hf_anti_sl hM hθ hF hs hL (Set.mem_Ici.1 hsl) hle (d + ε))
  linarith

theorem G_neg (hM : M.Standing) (hθ : M.hp ≤ (1 - M.γ) * M.θ) {F : (Fin L → ℝ) → ℝ}
    (hF : Inv F) {s : Fin L → ℝ} (hs : s ∈ stateSpace L) (hL : 0 < L) {sl : ℝ}
    (hsl : sLast s ≤ sl) (hsl0 : sl ≤ 0) {d : ℝ} (hd : M.dlo ≤ d) :
    M.G F s sl d = M.Pi sl d + M.γ * F 0 := by
  have := hM.isProbabilityMeasure
  rw [G_eq hM hθ hF hs hL hsl]
  have : ∫ ε, Hf M F s sl (d + ε) ∂M.μ = ∫ _ε, M.γ * F 0 ∂M.μ :=
    integral_congr_ae ((ae_t_nonneg hM hd).mono fun ε h => Hf_neg hM hF hs hL hsl hsl0 h)
  rw [this]
  simp

theorem C4_of_inv (hM : M.Standing) (hback : (1 - M.γ) * M.c ≤ M.hm)
    (hθ : M.hp ≤ (1 - M.γ) * M.θ) {F : (Fin L → ℝ) → ℝ}
    (hF : Inv F) {s : Fin L → ℝ} (hs : s ∈ stateSpace L) (hL : 0 < L) {d : ℝ}
    (hd : M.dlo ≤ d) :
    MonotoneOn (fun sl => M.G F s sl d) (Set.Icc (sLast s) 0) := by
  intro sl hsl sl' hsl' hle
  simp only
  rw [G_neg hM hθ hF hs hL hsl.1 hsl.2 hd, G_neg hM hθ hF hs hL hsl'.1 hsl'.2 hd]
  unfold Model.Pi
  have := integral_mono_ae (integrable_of_continuous hM (v_continuous M sl d))
    (integrable_of_continuous hM (v_continuous M sl' d))
    ((ae_t_nonneg hM hd).mono fun ε h => v_mono_neg hback hle (le_trans hsl'.2 h))
  linarith

end PartB

/-! ## Part C: the induction `Inv (f n)`, and C1, C4 for every `n`. -/

section PartC

variable {L : ℕ} {M : Model}

abbrev Aset (M : Model) (F : (Fin L → ℝ) → ℝ) (s : Fin L → ℝ) : Set ℝ :=
  (fun p : ℝ × ℝ => M.G F s p.1 p.2) '' {p | sLast s ≤ p.1 ∧ p.2 ∈ Set.Icc M.dlo M.dhi}

theorem Aset_nonempty (hM : M.Standing) (F : (Fin L → ℝ) → ℝ) (s : Fin L → ℝ) :
    (Aset M F s).Nonempty :=
  ⟨_, ⟨(sLast s, M.dlo), ⟨le_rfl, le_rfl, hM.dlo_le_dhi⟩, rfl⟩⟩

theorem Aset_bdd (hM : M.Standing) (hback : (1 - M.γ) * M.c ≤ M.hm)
    (hθ : M.hp ≤ (1 - M.γ) * M.θ) {F : (Fin L → ℝ) → ℝ} (hF : Inv F) {s : Fin L → ℝ}
    (hs : s ∈ stateSpace L) (hL : 0 < L) : BddAbove (Aset M F s) := by
  obtain ⟨R, hR⟩ := (isCompact_Icc (a := M.dlo) (b := M.dhi)).bddAbove_image
    hM.revenue_continuousOn
  refine ⟨R + M.γ * F 0, ?_⟩
  rintro _ ⟨⟨sl, d⟩, ⟨hsl, hd⟩, rfl⟩
  show M.G F s sl d ≤ R + M.γ * F 0
  have := hM.isProbabilityMeasure
  rw [G_eq hM hθ hF hs hL hsl]
  unfold Model.Pi
  have h1 : ∫ ε, M.v sl (d + ε) ∂M.μ ≤ 0 :=
    integral_nonpos_of_ae ((ae_t_nonneg hM hd.1).mono fun ε h => v_nonpos hM hback h)
  have h2 : ∫ ε, Hf M F s sl (d + ε) ∂M.μ ≤ M.γ * F 0 := by
    have := integral_mono (Hf_integrable hM hθ hF hs hL hsl d) (integrable_const (M.γ * F 0))
      (fun ε => Hf_le hM hθ hF hs hL hsl _)
    simpa using this
  have h3 : M.P d * d ≤ R := hR (Set.mem_image_of_mem (fun d => M.P d * d) hd)
  linarith

theorem inv_step (hM : M.Standing) (hback : (1 - M.γ) * M.c ≤ M.hm)
    (hθ : M.hp ≤ (1 - M.γ) * M.θ) (hL : 0 < L) {F : (Fin L → ℝ) → ℝ} (hF : Inv F) :
    Inv (fun s => sSup (Aset M F s)) := by
  constructor
  · intro x hx y hy hle
    show sSup (Aset M F y) ≤ sSup (Aset M F x)
    apply csSup_le (Aset_nonempty hM F y)
    rintro _ ⟨⟨sl, d⟩, ⟨hsl, hd⟩, rfl⟩
    have hslx : sLast x ≤ sl := (sLast_mono hle).trans hsl
    refine le_trans ?_ (le_csSup (Aset_bdd hM hback hθ hF hx hL) ⟨(sl, d), ⟨hslx, hd⟩, rfl⟩)
    show M.G F y sl d ≤ M.G F x sl d
    rw [G_eq hM hθ hF hy hL hsl, G_eq hM hθ hF hx hL hslx]
    have := integral_mono (Hf_integrable hM hθ hF hy hL hsl d)
      (Hf_integrable hM hθ hF hx hL hslx d) (fun ε => Hf_anti_s hM hθ hF hx hy hL hle hsl (d + ε))
    linarith
  · intro y hy
    show sSup (Aset M F y) = sSup (Aset M F (posPart y))
    have hy' := posPart_mem hy
    have hGeq : ∀ sl d, sLast y ≤ sl → 0 ≤ sl → M.dlo ≤ d →
        M.G F y sl d = M.G F (posPart y) sl d := by
      intro sl d hsl h0 hd
      have hsl' : sLast (posPart y) ≤ sl := by rw [sLast_posPart]; exact max_le hsl h0
      rw [G_eq hM hθ hF hy hL hsl, G_eq hM hθ hF hy' hL hsl']
      congr 1
      exact integral_congr_ae ((ae_t_nonneg hM hd).mono fun ε h => Hf_posPart hF hy hsl h0 h)
    apply le_antisymm
    · apply csSup_le (Aset_nonempty hM F y)
      rintro _ ⟨⟨sl, d⟩, ⟨hsl, hd⟩, rfl⟩
      show M.G F y sl d ≤ _
      by_cases h0 : 0 ≤ sl
      · rw [hGeq sl d hsl h0 hd.1]
        exact le_csSup (Aset_bdd hM hback hθ hF hy' hL)
          ⟨(sl, d), ⟨by rw [sLast_posPart]; exact max_le hsl h0, hd⟩, rfl⟩
      · push Not at h0
        have h1 : M.G F y sl d ≤ M.G F y 0 d :=
          C4_of_inv hM hback hθ hF hy hL hd.1 ⟨hsl, h0.le⟩ ⟨hsl.trans h0.le, le_rfl⟩ h0.le
        rw [hGeq 0 d (hsl.trans h0.le) le_rfl hd.1] at h1
        refine h1.trans (le_csSup (Aset_bdd hM hback hθ hF hy' hL) ⟨(0, d), ⟨?_, hd⟩, rfl⟩)
        rw [sLast_posPart]
        exact max_le (hsl.trans h0.le) le_rfl
    · apply csSup_le (Aset_nonempty hM F _)
      rintro _ ⟨⟨sl, d⟩, ⟨hsl, hd⟩, rfl⟩
      rw [sLast_posPart] at hsl
      have hsl1 : sLast y ≤ sl := le_trans (le_max_left _ _) hsl
      have hsl0 : 0 ≤ sl := le_trans (le_max_right _ _) hsl
      show M.G F (posPart y) sl d ≤ _
      rw [← hGeq sl d hsl1 hsl0 hd.1]
      exact le_csSup (Aset_bdd hM hback hθ hF hy hL) ⟨(sl, d), ⟨hsl1, hd⟩, rfl⟩

theorem inv_f (hM : M.Standing) (hback : (1 - M.γ) * M.c ≤ M.hm)
    (hθ : M.hp ≤ (1 - M.γ) * M.θ) (hL : 0 < L) (n : ℕ) :
    Inv (M.f n : (Fin L → ℝ) → ℝ) := by
  induction n with
  | zero => exact ⟨fun _ _ _ _ _ => le_rfl, fun _ _ => rfl⟩
  | succ n ih => exact inv_step hM hback hθ hL ih

end PartC

/-- Child C1 (all `n`). -/
theorem C1_full (M : Model) (hM : M.Standing) (L : ℕ) (hL : 1 ≤ L)
    (hback : (1 - M.γ) * M.c ≤ M.hm) (hθ : M.hp ≤ (1 - M.γ) * M.θ) (n : ℕ)
    (s : Fin L → ℝ) (hs : s ∈ stateSpace L) (d : ℝ) :
    AntitoneOn (fun sl => M.G (M.f n) s sl d - M.Pi sl d) (Set.Ici (sLast s)) :=
  C1_of_inv hM hθ (inv_f hM hback hθ (by omega) n) hs (by omega) d

/-- Child C4 (all `n`). -/
theorem C4_full (M : Model) (hM : M.Standing) (L : ℕ) (hL : 1 ≤ L)
    (hback : (1 - M.γ) * M.c ≤ M.hm) (hθ : M.hp ≤ (1 - M.γ) * M.θ) (n : ℕ)
    (s : Fin L → ℝ) (hs : s ∈ stateSpace L) (d : ℝ) (hd : d ∈ Set.Icc M.dlo M.dhi) :
    MonotoneOn (fun sl => M.G (M.f n) s sl d) (Set.Icc (sLast s) 0) :=
  C4_of_inv hM hback hθ (inv_f hM hback hθ (by omega) n) hs (by omega) hd.1

/-! ## Part D: the slope invariant `Qall` and C2 (given monotonicity of `Π̃(·, d')` on `[0, τ]`). -/

section PartD

variable {L : ℕ} {M : Model}

theorem bump_apply (y : Fin L → ℝ) (i j : Fin L) (δ : ℝ) :
    (y + Pi.single i δ : Fin L → ℝ) j = y j + if (j : ℕ) = i then δ else 0 := by
  simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]

theorem le_bump (y : Fin L → ℝ) (i : Fin L) {δ : ℝ} (hδ : 0 ≤ δ) : y ≤ y + Pi.single i δ := by
  intro j
  rw [bump_apply]
  split_ifs <;> linarith

theorem sLast_bump (y : Fin L → ℝ) (i : Fin L) (δ : ℝ) :
    sLast (y + Pi.single i δ) = sLast y + if (i : ℕ) + 1 = L then δ else 0 := by
  have hL : 0 < L := Fin.pos i
  have := i.isLt
  rw [sLast_eq _ hL, sLast_eq _ hL, bump_apply]
  simp only [Fin.val_mk]
  split_ifs <;> first | omega | rfl

theorem sFirst_bump (y : Fin L → ℝ) (i : Fin L) (δ : ℝ) :
    sFirst (y + Pi.single i δ) = sFirst y + if (i : ℕ) = 0 then δ else 0 := by
  have hL : 0 < L := Fin.pos i
  rw [sFirst_eq _ hL, sFirst_eq _ hL, bump_apply]
  simp only [Fin.val_mk]
  split_ifs <;> first | omega | rfl

theorem next_bump_zero (y : Fin L → ℝ) (i : Fin L) (hi : (i : ℕ) = 0) (δ sl a : ℝ) :
    next (y + Pi.single i δ) sl a = next y sl a := by
  funext j
  rw [next_apply, next_apply]
  split_ifs with hj
  · rw [bump_apply]
    simp only [Fin.val_mk]
    rw [if_neg (by omega)]
    ring
  · rfl

theorem next_bump_succ (y : Fin L → ℝ) (i : Fin L) (hi : 0 < (i : ℕ)) (δ sl a : ℝ) :
    next (y + Pi.single i δ) sl a
      = next y sl a + Pi.single (⟨(i : ℕ) - 1, by omega⟩ : Fin L) δ := by
  have := i.isLt
  funext j
  have := j.isLt
  rw [Pi.add_apply, next_apply, next_apply]
  simp only [Pi.single_apply, Fin.ext_iff, Fin.val_mk]
  by_cases hj : (j : ℕ) + 1 < L
  · rw [dif_pos hj, dif_pos hj, bump_apply]
    simp only [Fin.val_mk]
    split_ifs <;> first | omega | ring
  · rw [dif_neg hj, dif_neg hj]
    split_ifs <;> first | omega | ring

theorem next_sl_bump (s : Fin L → ℝ) (hL : 0 < L) (sl sl' a : ℝ) :
    next s sl' a = next s sl a + Pi.single (⟨L - 1, by omega⟩ : Fin L) (sl' - sl) := by
  funext j
  have := j.isLt
  rw [Pi.add_apply, next_apply, next_apply]
  simp only [Pi.single_apply, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | omega | ring

/-- The slope invariant: raising coordinate `i` by `δ` costs at most `γ^i θ̃ δ`
(for the last coordinate only while it stays `≤ τ`). -/
def Qall (M : Model) (τ : ℝ) (F : (Fin L → ℝ) → ℝ) : Prop :=
  ∀ y ∈ stateSpace L, ∀ (i : Fin L) (δ : ℝ), 0 ≤ δ → y + Pi.single i δ ∈ stateSpace L →
    ((i : ℕ) + 1 = L → y i + δ ≤ τ) → F y - M.γ ^ (i : ℕ) * M.θt * δ ≤ F (y + Pi.single i δ)

theorem Hf_ge (hM : M.Standing) {F : (Fin L → ℝ) → ℝ}
    (hF : Inv F) {s : Fin L → ℝ} (hs : s ∈ stateSpace L) (hL : 0 < L) {sl t : ℝ}
    (hsl : sLast s ≤ sl) (hslt : sl ≤ t) : Hf M F s sl t = M.γ * F 0 := by
  have hI : Ival s sl t = {t} := by
    unfold Ival
    rw [max_eq_right (by linarith [sFirst_le_sLast hs hL] : sFirst s ≤ t),
      max_eq_right hslt, Set.Icc_self]
  unfold Hf
  rw [hI, Set.image_singleton, csSup_singleton]
  unfold hfun
  rw [hF.eq_zero (next_mem hs hsl t) (next_le_zero hs hsl hslt)]
  ring

theorem Hf_bump (hM : M.Standing) (hθ : M.hp ≤ (1 - M.γ) * M.θ) {τ : ℝ}
    {F : (Fin L → ℝ) → ℝ} (hF : Inv F) (hQ : Qall M τ F) {y : Fin L → ℝ}
    (hy : y ∈ stateSpace L) (hL : 0 < L) (i : Fin L) {δ : ℝ} (hδ : 0 ≤ δ)
    (hy' : y + Pi.single i δ ∈ stateSpace L) {sl : ℝ} (hsl : sLast (y + Pi.single i δ) ≤ sl)
    (t : ℝ) :
    Hf M F y sl t - M.γ ^ (i : ℕ) * M.θt * δ ≤ Hf M F (y + Pi.single i δ) sl t := by
  have hsly : sLast y ≤ sl := le_trans (sLast_mono (le_bump y i hδ)) hsl
  have hθ0 := θt_nonneg M hM hθ
  rw [sub_le_iff_le_add]
  apply csSup_le ((Ival_nonempty hy hL hsly t).image _)
  rintro _ ⟨a, ha, rfl⟩
  rw [← sub_le_iff_le_add]
  by_cases hi0 : (i : ℕ) = 0
  · have hs1 : sFirst (y + Pi.single i δ) = y i + δ := by
      rw [sFirst_bump, if_pos hi0, sFirst_eq _ hL]
      congr 2
      exact Fin.ext hi0.symm
    have hyi : y i ≤ a := by
      have : sFirst y = y i := by rw [sFirst_eq _ hL]; congr 1; exact Fin.ext hi0.symm
      rw [← this]; exact le_trans (le_max_left _ _) ha.1
    have hyi' : (y + Pi.single i δ : Fin L → ℝ) i = y i + δ := by rw [bump_apply, if_pos rfl]
    have ha' : max a (y i + δ) ∈ Ival (y + Pi.single i δ) sl t := by
      refine ⟨?_, max_le ha.2 ?_⟩
      · rw [hs1]
        exact max_le (le_max_right _ _) (le_trans (le_trans (le_max_right _ _) ha.1)
          (le_max_left _ _))
      · rw [← hyi']; exact le_trans ((le_sLast hy' i).trans hsl) (le_max_left _ _)
    refine le_trans ?_ (le_Hf hM hθ hF hy' hsl ha')
    unfold hfun
    rw [next_bump_zero y i hi0, hi0, pow_zero, one_mul]
    have h1 := hF.anti _ (next_mem hy hsly _) _ (next_mem hy hsly a)
      (next_anti_a y sl (le_max_left a (y i + δ)))
    have h2 := mul_le_mul_of_nonneg_left h1 hM.γ_nonneg
    have h3 : max a (y i + δ) ≤ a + δ := max_le (by linarith) (by linarith)
    have h4 := mul_le_mul_of_nonneg_left h3 hθ0
    nlinarith
  · have hipos : 0 < (i : ℕ) := Nat.pos_of_ne_zero hi0
    have hIeq : Ival (y + Pi.single i δ) sl t = Ival y sl t := by
      unfold Ival; rw [sFirst_bump, if_neg hi0, add_zero]
    have ha' : a ∈ Ival (y + Pi.single i δ) sl t := by rw [hIeq]; exact ha
    refine le_trans ?_ (le_Hf hM hθ hF hy' hsl ha')
    unfold hfun
    rw [next_bump_succ y i hipos]
    have hmem : next y sl a + Pi.single (⟨(i : ℕ) - 1, by omega⟩ : Fin L) δ ∈ stateSpace L := by
      rw [← next_bump_succ y i hipos]; exact next_mem hy' hsl a
    have hQ' := hQ (next y sl a) (next_mem hy hsly a) ⟨(i : ℕ) - 1, by omega⟩ δ hδ hmem
      (fun h => absurd h (by simp only [Fin.val_mk]; omega))
    have h2 := mul_le_mul_of_nonneg_left hQ' hM.γ_nonneg
    have e : M.γ * (M.γ ^ ((i : ℕ) - 1) * M.θt * δ) = M.γ ^ (i : ℕ) * M.θt * δ := by
      have : (i : ℕ) = ((i : ℕ) - 1) + 1 := by omega
      conv_rhs => rw [this, pow_succ]
      ring
    simp only [Fin.val_mk] at h2
    nlinarith

theorem K_ge (hM : M.Standing) (L : ℕ) : M.γ ^ L * M.θt ≤ M.K L := by
  unfold Model.K
  have : 0 ≤ ∑ j ∈ Finset.Ico 1 L, M.γ ^ j * M.hp :=
    Finset.sum_nonneg fun j _ => mul_nonneg (pow_nonneg hM.γ_nonneg j) hM.hp_nonneg
  linarith

theorem Hf_C2pt (hM : M.Standing) (hθ : M.hp ≤ (1 - M.γ) * M.θ) {τ : ℝ}
    {F : (Fin L → ℝ) → ℝ} (hF : Inv F) (hQ : Qall M τ F) {s : Fin L → ℝ}
    (hs : s ∈ stateSpace L) (hL : 0 < L) {sl sl' t : ℝ} (hsl : sLast s ≤ sl) (hll : sl ≤ sl')
    (hτ : sl' - t ≤ τ) :
    Hf M F s sl t - M.K L * (max (sl' - t) 0 - max (sl - t) 0) ≤ Hf M F s sl' t := by
  have hθ0 := θt_nonneg M hM hθ
  have hK := K_ge hM L
  have hγ0 := hM.γ_nonneg
  have hsl' : sLast s ≤ sl' := hsl.trans hll
  have eγ : M.γ * (M.γ ^ (L - 1) * M.θt) = M.γ ^ L * M.θt := by
    have : L = (L - 1) + 1 := by omega
    conv_rhs => rw [this, pow_succ]
    ring
  rcases le_total sl' t with h1 | h1
  · rw [Hf_ge hM hF hs hL hsl (hll.trans h1), Hf_ge hM hF hs hL hsl' h1,
      max_eq_right (by linarith : sl' - t ≤ 0), max_eq_right (by linarith : sl - t ≤ 0)]
    linarith
  rcases le_total sl t with h2 | h2
  · -- sl ≤ t ≤ sl'
    rw [Hf_ge hM hF hs hL hsl h2, max_eq_left (by linarith : 0 ≤ sl' - t),
      max_eq_right (by linarith : sl - t ≤ 0)]
    have ht : t ∈ Ival s sl' t :=
      ⟨max_le (by linarith [sFirst_le_sLast hs hL]) le_rfl, le_max_right _ _⟩
    refine le_trans ?_ (le_Hf hM hθ hF hs hsl' ht)
    unfold hfun
    have hpos : posPart (next s sl' t)
        = (0 : Fin L → ℝ) + Pi.single (⟨L - 1, by omega⟩ : Fin L) (sl' - t) := by
      funext j
      have := j.isLt
      simp only [posPart, Pi.add_apply, Pi.zero_apply, zero_add, Pi.single_apply, Fin.ext_iff,
        Fin.val_mk, next_apply]
      split_ifs with hj hj'
      · omega
      · exact max_eq_right (by linarith [le_sLast hs ⟨(j : ℕ) + 1, hj⟩])
      · exact max_eq_left (by linarith)
      · omega
    have hmem : (0 : Fin L → ℝ) + Pi.single (⟨L - 1, by omega⟩ : Fin L) (sl' - t)
        ∈ stateSpace L := by
      rw [← hpos]; exact posPart_mem (next_mem hs hsl' t)
    have hQ' := hQ 0 zero_mem ⟨L - 1, by omega⟩ (sl' - t) (by linarith) hmem
      (fun _ => by simp only [Pi.zero_apply]; linarith)
    rw [← hpos, ← hF.pos _ (next_mem hs hsl' t)] at hQ'
    simp only [Fin.val_mk] at hQ'
    have h3 := mul_le_mul_of_nonneg_left hQ' hγ0
    have h4 := mul_le_mul_of_nonneg_left hK (by linarith : (0 : ℝ) ≤ sl' - t)
    nlinarith
  · -- t ≤ sl
    rw [max_eq_left (by linarith : 0 ≤ sl' - t), max_eq_left (by linarith : 0 ≤ sl - t)]
    rw [sub_le_iff_le_add]
    apply csSup_le ((Ival_nonempty hs hL hsl t).image _)
    rintro _ ⟨a, ha, rfl⟩
    rw [← sub_le_iff_le_add]
    have hat : t ≤ a := le_trans (le_max_right _ _) ha.1
    have has : a ≤ sl := by have := ha.2; rwa [max_eq_left h2] at this
    have ha' : a ∈ Ival s sl' t := ⟨ha.1, ha.2.trans (max_le_max hll le_rfl)⟩
    refine le_trans ?_ (le_Hf hM hθ hF hs hsl' ha')
    unfold hfun
    rw [next_sl_bump s hL sl sl' a]
    have hmem : next s sl a + Pi.single (⟨L - 1, by omega⟩ : Fin L) (sl' - sl) ∈ stateSpace L := by
      rw [← next_sl_bump s hL sl sl' a]; exact next_mem hs hsl' a
    have hQ' := hQ (next s sl a) (next_mem hs hsl a) ⟨L - 1, by omega⟩ (sl' - sl)
      (by linarith) hmem (fun _ => by
        rw [next_apply, dif_neg (by simp only [Fin.val_mk]; omega)]; linarith)
    simp only [Fin.val_mk] at hQ'
    have h3 := mul_le_mul_of_nonneg_left hQ' hγ0
    have h4 := mul_le_mul_of_nonneg_left hK (by linarith : (0 : ℝ) ≤ sl' - sl)
    nlinarith

theorem C2_gen (hM : M.Standing) (hθ : M.hp ≤ (1 - M.γ) * M.θ) {τ : ℝ}
    {F : (Fin L → ℝ) → ℝ} (hF : Inv F) (hQ : Qall M τ F) {s : Fin L → ℝ}
    (hs : s ∈ stateSpace L) (hL : 0 < L) {d : ℝ} {U : ℝ} (hU : U ≤ d + M.A + τ) :
    MonotoneOn (fun sl => M.G F s sl d - M.PiT L sl d) (Set.Icc (sLast s) U) := by
  intro sl hsl sl' hsl' hle
  show M.G F s sl d - M.PiT L sl d ≤ M.G F s sl' d - M.PiT L sl' d
  rw [G_eq hM hθ hF hs hL hsl.1, G_eq hM hθ hF hs hL hsl'.1]
  unfold Model.PiT
  have i1 := Hf_integrable hM hθ hF hs hL hsl.1 d
  have i2 := Hf_integrable hM hθ hF hs hL hsl'.1 d
  have j1 : Integrable (fun ε => max (sl - (d + ε)) 0) M.μ :=
    integrable_of_continuous hM (by fun_prop)
  have j2 : Integrable (fun ε => max (sl' - (d + ε)) 0) M.μ :=
    integrable_of_continuous hM (by fun_prop)
  have h2 : Integrable (fun ε => M.K L * (max (sl' - (d + ε)) 0 - max (sl - (d + ε)) 0)) M.μ :=
    (j2.sub j1).const_mul _
  have hmono : ∫ ε, (Hf M F s sl (d + ε)
      - M.K L * (max (sl' - (d + ε)) 0 - max (sl - (d + ε)) 0)) ∂M.μ
      ≤ ∫ ε, Hf M F s sl' (d + ε) ∂M.μ :=
    integral_mono_ae (i1.sub h2) i2
      ((ae_mem hM).mono fun ε hε => Hf_C2pt hM hθ hF hQ hs hL hsl.1 hle
        (by linarith [hε.1, hsl'.2]))
  rw [integral_sub i1 h2, integral_const_mul, integral_sub j2 j1] at hmono
  have h5 := mul_le_mul_of_nonneg_left hle (mul_nonneg hM.γ_nonneg hM.c_nonneg)
  linarith

theorem G_mono_tau (hM : M.Standing) (hback : (1 - M.γ) * M.c ≤ M.hm)
    (hθ : M.hp ≤ (1 - M.γ) * M.θ) {τ : ℝ}
    {F : (Fin L → ℝ) → ℝ} (hF : Inv F) (hQ : Qall M τ F)
    (hτ : ∀ d' ∈ Set.Icc M.dlo M.dhi, MonotoneOn (fun sl => M.PiT L sl d') (Set.Icc 0 τ))
    {s : Fin L → ℝ} (hs : s ∈ stateSpace L) (hL : 0 < L) {d : ℝ}
    (hd : d ∈ Set.Icc M.dlo M.dhi) :
    MonotoneOn (fun sl => M.G F s sl d) (Set.Icc (sLast s) τ) := by
  have h2 := C2_gen hM hθ hF hQ hs hL (d := d) (U := τ)
    (by linarith [hd.1, hM.demand_nonneg])
  have h4 := C4_of_inv hM hback hθ hF hs hL hd.1
  have h3 := hτ d hd
  have pos_case : ∀ x y, x ∈ Set.Icc (sLast s) τ → y ∈ Set.Icc (sLast s) τ → 0 ≤ x → x ≤ y →
      M.G F s x d ≤ M.G F s y d := by
    intro x y hx hy hx0 hxy
    have a1 : M.G F s x d - M.PiT L x d ≤ M.G F s y d - M.PiT L y d := h2 hx hy hxy
    have a2 : M.PiT L x d ≤ M.PiT L y d := h3 ⟨hx0, hx.2⟩ ⟨hx0.trans hxy, hy.2⟩ hxy
    linarith
  intro x hx y hy hxy
  show M.G F s x d ≤ M.G F s y d
  by_cases hy0 : y ≤ 0
  · exact h4 ⟨hx.1, hxy.trans hy0⟩ ⟨hy.1, hy0⟩ hxy
  by_cases hx0 : 0 ≤ x
  · exact pos_case x y hx hy hx0 hxy
  push Not at hy0 hx0
  have b1 : M.G F s x d ≤ M.G F s 0 d := h4 ⟨hx.1, hx0.le⟩ ⟨hx.1.trans hx0.le, le_rfl⟩ hx0.le
  have b2 := pos_case 0 y ⟨hx.1.trans hx0.le, hy0.le.trans hy.2⟩ hy le_rfl hy0.le
  linarith

theorem G_bump (hM : M.Standing) (hθ : M.hp ≤ (1 - M.γ) * M.θ) {τ : ℝ}
    {F : (Fin L → ℝ) → ℝ} (hF : Inv F) (hQ : Qall M τ F) {y : Fin L → ℝ}
    (hy : y ∈ stateSpace L) (hL : 0 < L) (i : Fin L) {δ : ℝ} (hδ : 0 ≤ δ)
    (hy' : y + Pi.single i δ ∈ stateSpace L) {sl : ℝ} (hsl : sLast (y + Pi.single i δ) ≤ sl)
    (d : ℝ) :
    M.G F y sl d - M.γ ^ (i : ℕ) * M.θt * δ ≤ M.G F (y + Pi.single i δ) sl d := by
  have := hM.isProbabilityMeasure
  have hsly : sLast y ≤ sl := le_trans (sLast_mono (le_bump y i hδ)) hsl
  rw [G_eq hM hθ hF hy hL hsly, G_eq hM hθ hF hy' hL hsl]
  have i1 := Hf_integrable hM hθ hF hy hL hsly d
  have i2 := Hf_integrable hM hθ hF hy' hL hsl d
  have i3 : Integrable (fun _ε : ℝ => M.γ ^ (i : ℕ) * M.θt * δ) M.μ := integrable_const _
  have hm : ∫ ε, (Hf M F y sl (d + ε) - M.γ ^ (i : ℕ) * M.θt * δ) ∂M.μ
      ≤ ∫ ε, Hf M F (y + Pi.single i δ) sl (d + ε) ∂M.μ :=
    integral_mono (i1.sub i3) i2 (fun ε => Hf_bump hM hθ hF hQ hy hL i hδ hy' hsl (d + ε))
  have hc : ∫ _ε, M.γ ^ (i : ℕ) * M.θt * δ ∂M.μ = M.γ ^ (i : ℕ) * M.θt * δ := by simp
  rw [integral_sub i1 i3, hc] at hm
  linarith

theorem Qall_step (hM : M.Standing) (hback : (1 - M.γ) * M.c ≤ M.hm)
    (hθ : M.hp ≤ (1 - M.γ) * M.θ) (hL : 0 < L) {τ : ℝ}
    (hτ : ∀ d' ∈ Set.Icc M.dlo M.dhi, MonotoneOn (fun sl => M.PiT L sl d') (Set.Icc 0 τ))
    {F : (Fin L → ℝ) → ℝ} (hF : Inv F) (hQ : Qall M τ F) :
    Qall M τ (fun s => sSup (Aset M F s)) := by
  intro y hy i δ hδ hy' hreg
  beta_reduce
  rw [sub_le_iff_le_add]
  apply csSup_le (Aset_nonempty hM F y)
  rintro _ ⟨⟨sl, d⟩, ⟨hsl, hd⟩, rfl⟩
  show M.G F y sl d ≤ _
  have key : ∀ sl'', sLast (y + Pi.single i δ) ≤ sl'' →
      M.G F y sl'' d - M.γ ^ (i : ℕ) * M.θt * δ ≤ sSup (Aset M F (y + Pi.single i δ)) :=
    fun sl'' h => (G_bump hM hθ hF hQ hy hL i hδ hy' h d).trans
      (le_csSup (Aset_bdd hM hback hθ hF hy' hL) ⟨(sl'', d), ⟨h, hd⟩, rfl⟩)
  by_cases h : sLast (y + Pi.single i δ) ≤ sl
  · linarith [key sl h]
  · push Not at h
    have hlast : (i : ℕ) + 1 = L := by
      by_contra hne
      rw [sLast_bump, if_neg hne, add_zero] at h
      linarith
    have hτ' : sLast (y + Pi.single i δ) ≤ τ := by
      rw [sLast_bump, if_pos hlast, sLast_eq _ hL]
      have e : (⟨L - 1, by omega⟩ : Fin L) = i := Fin.ext (by simp only [Fin.val_mk]; omega)
      rw [e]
      exact hreg hlast
    have hm := G_mono_tau hM hback hθ hF hQ hτ hy hL hd ⟨hsl, h.le.trans hτ'⟩
      ⟨hsl.trans h.le, hτ'⟩ h.le
    have := key _ le_rfl
    simp only at hm
    linarith

theorem Qall_f (hM : M.Standing) (hback : (1 - M.γ) * M.c ≤ M.hm)
    (hθ : M.hp ≤ (1 - M.γ) * M.θ) (hL : 0 < L) {τ : ℝ}
    (hτ : ∀ d' ∈ Set.Icc M.dlo M.dhi, MonotoneOn (fun sl => M.PiT L sl d') (Set.Icc 0 τ))
    (n : ℕ) : Qall M τ (M.f n : (Fin L → ℝ) → ℝ) := by
  induction n with
  | zero =>
    intro y _ i δ hδ _ _
    show (0 : ℝ) - M.γ ^ (i : ℕ) * M.θt * δ ≤ 0
    have := mul_nonneg (mul_nonneg (pow_nonneg hM.γ_nonneg (i : ℕ)) (θt_nonneg M hM hθ)) hδ
    linarith
  | succ n ih => exact Qall_step hM hback hθ hL hτ (inv_f hM hback hθ hL n) ih

end PartD

/-! ## Part E: monotonicity of `Π̃(·, d')` on `[0, S̲(d) − d − A]`, and C2. -/

section PartE

variable {L : ℕ} {M : Model}

theorem PiT_shift (hM : M.Standing) (L : ℕ) (d d' x : ℝ) :
    M.PiT L x d' = M.PiT L (x - d' + d) d
      + (M.P d' * d' - M.P d * d - M.c * (d' - d) - M.γ * M.c * (d' - d)) := by
  have := hM.isProbabilityMeasure
  have hv : ∀ ε, M.v x (d' + ε) = M.v (x - d' + d) (d + ε) - M.c * (d' - d) := by
    intro ε
    unfold Model.v
    rw [show x - d' + d - (d + ε) = x - (d' + ε) by ring,
      show d + ε - (x - d' + d) = d' + ε - x by ring]
    ring
  have hm : ∀ ε, max (x - (d' + ε)) 0 = max (x - d' + d - (d + ε)) 0 := by
    intro ε
    rw [show x - d' + d - (d + ε) = x - (d' + ε) by ring]
  have hI : ∫ ε, (M.v (x - d' + d) (d + ε) - M.c * (d' - d)) ∂M.μ
      = ∫ ε, M.v (x - d' + d) (d + ε) ∂M.μ - M.c * (d' - d) := by
    rw [integral_sub (integrable_of_continuous hM (v_continuous M _ d)) (integrable_const _)]
    simp
  unfold Model.PiT Model.Pi
  simp_rw [hv, hm]
  rw [hI]
  ring

theorem PiT_concave (hM : M.Standing) (hγ : M.γ < 1) (hθ : M.hp ≤ (1 - M.γ) * M.θ)
    (L : ℕ) (d : ℝ) : ConcaveOn ℝ Set.univ (fun sl => M.PiT L sl d) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have hPi := (Thm3Red.Pi_concave M hM d).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  simp only [smul_eq_mul] at hPi
  have hK := Thm3Red.K_nonneg M hM L hγ hθ
  have jx : Integrable (fun ε => max (x - (d + ε)) 0) M.μ :=
    integrable_of_continuous hM (by fun_prop)
  have jy : Integrable (fun ε => max (y - (d + ε)) 0) M.μ :=
    integrable_of_continuous hM (by fun_prop)
  have jz : Integrable (fun ε => max (a * x + b * y - (d + ε)) 0) M.μ :=
    integrable_of_continuous hM (by fun_prop)
  have hmx : ∫ ε, max (a * x + b * y - (d + ε)) 0 ∂M.μ
      ≤ ∫ ε, (a * max (x - (d + ε)) 0 + b * max (y - (d + ε)) 0) ∂M.μ :=
    integral_mono jz ((jx.const_mul a).add (jy.const_mul b))
      (fun ε => Thm3Red.max_comb_le a b x y (d + ε) ha hb hab)
  rw [integral_add (jx.const_mul a) (jy.const_mul b), integral_const_mul,
    integral_const_mul] at hmx
  have h1 := mul_le_mul_of_nonneg_left hmx hK
  unfold Model.PiT
  nlinarith

theorem concave_mono_left {f : ℝ → ℝ} (hf : ConcaveOn ℝ Set.univ f) {x0 : ℝ} (hx0 : 0 < x0)
    (hmax : ∀ y, 0 ≤ y → f y ≤ f x0) : ∀ z1 z2, z1 ≤ z2 → z2 ≤ x0 → f z1 ≤ f z2 := by
  have hglob : ∀ z, f z ≤ f x0 := by
    intro z
    by_cases hz : 0 ≤ z
    · exact hmax z hz
    push Not at hz
    have hd : 0 < x0 - z := by linarith
    set θ := x0 / (x0 - z) with hθdef
    have hθ0 : 0 < θ := div_pos hx0 hd
    have hθ1 : θ ≤ 1 := (div_le_one hd).2 (by linarith)
    have key := hf.2 (Set.mem_univ z) (Set.mem_univ x0) hθ0.le (by linarith : 0 ≤ 1 - θ)
      (by ring : θ + (1 - θ) = 1)
    simp only [smul_eq_mul] at key
    have hpt : θ * z + (1 - θ) * x0 = 0 := by
      rw [hθdef]; field_simp; ring
    rw [hpt] at key
    have h0 := hmax 0 le_rfl
    by_contra hc
    push Not at hc
    have := mul_lt_mul_of_pos_left hc hθ0
    nlinarith
  intro z1 z2 h12 h2
  rcases eq_or_lt_of_le (h12.trans h2) with he | hlt
  · have : z2 = z1 := by linarith
    rw [this]
  · have hd : 0 < x0 - z1 := by linarith
    set l := (x0 - z2) / (x0 - z1) with hldef
    have hl0 : 0 ≤ l := div_nonneg (by linarith) hd.le
    have hl1 : l ≤ 1 := (div_le_one hd).2 (by linarith)
    have key := hf.2 (Set.mem_univ z1) (Set.mem_univ x0) hl0 (by linarith : 0 ≤ 1 - l)
      (by ring : l + (1 - l) = 1)
    simp only [smul_eq_mul] at key
    have hpt : l * z1 + (1 - l) * x0 = z2 := by
      rw [hldef]; field_simp; ring
    rw [hpt] at key
    have := mul_le_mul_of_nonneg_left (hglob z1) (by linarith : 0 ≤ 1 - l)
    nlinarith

theorem Htau (hM : M.Standing) (hγ : M.γ < 1) (hθ : M.hp ≤ (1 - M.γ) * M.θ) (L : ℕ)
    {d : ℝ} (hd : d ∈ Set.Icc M.dlo M.dhi) {Sund : ℝ}
    (hSund : IsLargestMaxOn (fun sl => M.PiT L sl d) (Set.Ici 0) Sund) :
    ∀ d' ∈ Set.Icc M.dlo M.dhi,
      MonotoneOn (fun sl => M.PiT L sl d') (Set.Icc 0 (Sund - d - M.A)) := by
  intro d' hd' x hx y hy hxy
  show M.PiT L x d' ≤ M.PiT L y d'
  have hA := hM.demand_nonneg
  have hS0 : 0 ≤ Sund := hSund.1.1
  by_cases hpos : 0 < Sund
  · have hmono := concave_mono_left (PiT_concave hM hγ hθ L d) hpos
      (fun z hz => hSund.1.2 z hz)
    rw [PiT_shift hM L d d' x, PiT_shift hM L d d' y]
    have : M.PiT L (x - d' + d) d ≤ M.PiT L (y - d' + d) d :=
      hmono (x - d' + d) (y - d' + d) (by linarith) (by linarith [hy.2, hd'.1])
    linarith
  · have hS : Sund = 0 := le_antisymm (not_lt.1 hpos) hS0
    have : x = y := by linarith [hx.1, hx.2, hy.1, hy.2, hd.1]
    rw [this]

end PartE

/-- Child C2 (all `n`). -/
theorem C2_full (M : Model) (hM : M.Standing) (L : ℕ) (hL : 1 ≤ L)
    (hback : (1 - M.γ) * M.c ≤ M.hm) (hγ : M.γ < 1) (hθ : M.hp ≤ (1 - M.γ) * M.θ) (n : ℕ)
    (s : Fin L → ℝ) (hs : s ∈ stateSpace L) (d : ℝ) (hd : d ∈ Set.Icc M.dlo M.dhi)
    (Sund : ℝ) (hSund : IsLargestMaxOn (fun sl => M.PiT L sl d) (Set.Ici 0) Sund) :
    MonotoneOn (fun sl => M.G (M.f n) s sl d - M.PiT L sl d)
      (Set.Icc (max (sLast s) 0) Sund) :=
  (C2_gen hM hθ (inv_f hM hback hθ (by omega) n)
    (Qall_f hM hback hθ (by omega) (Htau hM hγ hθ L hd hSund) n) hs (by omega)
    (d := d) (U := Sund) (by linarith)).mono (Set.Icc_subset_Icc (le_max_left _ _) le_rfl)

end PerishablePricing.Bounds.Thm3Core

open PerishablePricing.Bounds in
theorem solution (M : Model) (hM : M.Standing) (L : ℕ) (hL : 1 ≤ L)
    (hback : (1 - M.γ) * M.c ≤ M.hm) (hγ : M.γ < 1) (hθ : M.hp ≤ (1 - M.γ) * M.θ) (n : ℕ)
    (s : Fin L → ℝ) (hs : s ∈ stateSpace L) (d : ℝ) (hd : d ∈ Set.Icc M.dlo M.dhi)
    (S Sbar Sund : ℝ)
    (hS : IsLargestMaxOn (fun sl => M.G (M.f n) s sl d) (Set.Ici (sLast s)) S)
    (hSbar : IsLargestMaxOn (fun sl => M.Pi sl d) (Set.Ici 0) Sbar)
    (hSund : IsLargestMaxOn (fun sl => M.PiT L sl d) (Set.Ici 0) Sund) :
    max Sund (sLast s) ≤ S ∧ S ≤ max Sbar (sLast s) := by
  exact Thm3Red.theorem_3_of_children
    (fun M hM L hL hback _ hθ n s hs d _ =>
      Thm3Core.C1_full M hM L hL hback hθ n s hs d)
    (fun M hM L hL hback hγ hθ n s hs d hd Sund hSund =>
      Thm3Core.C2_full M hM L hL hback hγ hθ n s hs d hd Sund hSund)
    (fun M hM L hL hback _ hθ n s hs d hd =>
      Thm3Core.C4_full M hM L hL hback hθ n s hs d hd)
    M hM L hL hback hγ hθ n s hs d hd S Sbar Sund hS hSbar hSund
