-- Prove2me | solution 1 for PorteusSS.generalized_sS_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T03:34:39.365994+00:00
-- url     : https://prove2.me/submissions/70c50519-8747-407b-ab1f-681e08340d41

import Mathlib
import Definitions.Def_PorteusSS_Functions
import Definitions.Def_PorteusSS_OrderingCost
import Definitions.Def_PorteusSS_Model

/-! # Porteus (s,S) staged library (leaf 3872a132 `PorteusSS.generalized_sS_optimal`)

Stage S1: concave-cost library for `IsOrderingCost` and the abstract structural (s,S) lemma
(no measure theory).
Stage S2: the core lemma `conv_quasiK` (convolution with a TP2 probability density maps the
class `C_0(K)` to quasi-`K`-convex functions), with its layer-cake and TP2 machinery.
Stage S3: regularity of `h_n = hStep m φ α f` (lower semicontinuity, coercivity, growth at
`-∞`), the first moment of a one-sided Pólya density, measurability/growth/integrability of the
next value function, the invariant `PInv`, and `QKHyp` for `h_n` (`qkhyp_hStep`), assembled in
`leaf_of_PInv`. -/

set_option autoImplicit false

open Filter Topology Set

namespace PorteusSS
namespace Lib

/-! ## S1 (a): concave ordering-cost library -/

section Cost

variable {c : ℝ → ℝ} {c0 K0 cInf KInf : ℝ}

theorem C1_K_nonneg (hc0 : c 0 = 0) {z : ℝ} {p : ℝ × ℝ} (hp : p ∈ C1 c z) : 0 ≤ p.2 := by
  have h := hp.2 0 le_rfl
  rw [hc0] at h
  linarith

/-- Two supporting lines of the same slope touching `c` on `[0,∞)` have the same intercept. -/
theorem C1_K_eq {z z' k K K' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') (h1 : (k, K) ∈ C1 c z)
    (h2 : (k, K') ∈ C1 c z') : K = K' := by
  have a1 := h1.1
  have a2 := h1.2 z' hz'
  have b1 := h2.1
  have b2 := h2.2 z hz
  simp only at a1 a2 b1 b2
  linarith

/-- Supporting slopes are antitone in the touching point. -/
theorem C1_slope_anti {z z' : ℝ} {p q : ℝ × ℝ} (hz : 0 ≤ z) (hzz : z < z') (hp : p ∈ C1 c z)
    (hq : q ∈ C1 c z') : q.1 ≤ p.1 := by
  have a1 := hp.1
  have a2 := hp.2 z' (by linarith)
  have b1 := hq.1
  have b2 := hq.2 z hz
  by_contra hlt
  push Not at hlt
  have : 0 < (q.1 - p.1) * (z' - z) := mul_pos (by linarith) (by linarith)
  nlinarith

theorem Kc_eq_of_C2 {z k K : ℝ} (hz : 0 < z) (h : (k, K) ∈ C2 c z) : Kc c k = K := by
  unfold Kc
  have hset : {K' : ℝ | ∃ z : ℝ, 0 < z ∧ (k, K') ∈ C2 c z} = {K} := by
    ext K'
    constructor
    · rintro ⟨z', hz', h'⟩
      exact C1_K_eq hz'.le hz.le h'.1 h.1
    · intro hK'
      rw [mem_singleton_iff] at hK'
      subst hK'
      exact ⟨z, hz, h⟩
  rw [hset, csInf_singleton]

theorem C2_nonempty (hc : IsOrderingCost c c0 K0 cInf KInf) {z : ℝ} (hz : 0 < z) :
    ∃ k K : ℝ, (k, K) ∈ C2 c z := by
  have hconc := hc.concave
  set L : Set ℝ := (fun y => (c z - c y) / (z - y)) '' Ico 0 z with hL
  have hLne : L.Nonempty := ⟨_, ⟨0, ⟨le_rfl, hz⟩, rfl⟩⟩
  have hLbdd : BddBelow L := by
    refine ⟨(c (z + 1) - c z) / (z + 1 - z), ?_⟩
    rintro _ ⟨y, ⟨hy0, hyz⟩, rfl⟩
    exact hconc.slope_anti_adjacent (mem_Ici.2 hy0) (mem_Ici.2 (by linarith)) hyz (by linarith)
  set k := sInf L with hk
  have hk_le : ∀ y, 0 ≤ y → y < z → k * (z - y) ≤ c z - c y := by
    intro y hy0 hyz
    have : k ≤ (c z - c y) / (z - y) := csInf_le hLbdd ⟨y, ⟨hy0, hyz⟩, rfl⟩
    rwa [le_div_iff₀ (by linarith)] at this
  have hk_ge : ∀ y, z < y → c y - c z ≤ k * (y - z) := by
    intro y hzy
    have : (c y - c z) / (y - z) ≤ k := by
      apply le_csInf hLne
      rintro _ ⟨y', ⟨hy0, hyz⟩, rfl⟩
      exact hconc.slope_anti_adjacent (mem_Ici.2 hy0) (mem_Ici.2 (by linarith)) hyz hzy
    rwa [div_le_iff₀ (by linarith)] at this
  refine ⟨k, c z - k * z, ⟨⟨by simp, ?_⟩, ?_⟩⟩
  · intro y hy
    simp only
    rcases lt_trichotomy y z with hyz | rfl | hzy
    · have := hk_le y hy hyz
      nlinarith
    · linarith
    · have := hk_ge y hzy
      nlinarith
  · intro q hq
    simp only
    have hq1 : q.1 ≤ k := by
      apply le_csInf hLne
      rintro _ ⟨y, ⟨hy0, hyz⟩, rfl⟩
      have a1 := hq.1
      have a2 := hq.2 y hy0
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    have a1 := hq.1
    nlinarith

/-- For `z > 0` there is a slope `k ∈ C` whose supporting line touches `c` at `z`. -/
theorem exists_slope (hc : IsOrderingCost c c0 K0 cInf KInf) {z : ℝ} (hz : 0 < z) :
    ∃ k ∈ slopeSet c, c z = k * z + Kc c k := by
  obtain ⟨k, K, h⟩ := C2_nonempty hc hz
  refine ⟨k, ⟨K, C1_K_nonneg hc.zero h.1, z, hz, h⟩, ?_⟩
  rw [Kc_eq_of_C2 hz h]
  exact h.1.1.symm

/-- Every line of `C` supports `c` on `[0,∞)`. -/
theorem le_supporting {k : ℝ} (hk : k ∈ slopeSet c) {y : ℝ} (hy : 0 ≤ y) :
    c y ≤ k * y + Kc c k := by
  obtain ⟨K, _, z, hz, h⟩ := hk
  rw [Kc_eq_of_C2 hz h]
  exact h.1.2 y hy

theorem Kc_nonneg {k : ℝ} (hk : k ∈ slopeSet c) : 0 ≤ Kc c k := by
  obtain ⟨K, hK, z, hz, h⟩ := hk
  rw [Kc_eq_of_C2 hz h]
  exact hK

theorem c_nonneg (hc : IsOrderingCost c c0 K0 cInf KInf) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ c y := by
  have := hc.mono (mem_Ici.2 le_rfl) (mem_Ici.2 hy) hy
  rwa [hc.zero] at this

theorem slope_nonneg (hc : IsOrderingCost c c0 K0 cInf KInf) {k : ℝ} (hk : k ∈ slopeSet c) :
    0 ≤ k := by
  obtain ⟨K, _, z, hz, h⟩ := hk
  have a1 := h.1.1
  have a2 := h.1.2 (z + 1) (by linarith)
  have a3 := hc.mono (mem_Ici.2 hz.le) (mem_Ici.2 (by linarith : (0:ℝ) ≤ z + 1)) (by linarith)
  simp only at a1 a2
  nlinarith

/-- Increments of a concave `c` decrease: `c (b+d) + c a ≤ c b + c (a+d)` for `0 ≤ a ≤ b`,
`0 ≤ d`. -/
theorem incr_anti (hc : IsOrderingCost c c0 K0 cInf KInf) {a b d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hd : 0 ≤ d) : c (b + d) + c a ≤ c b + c (a + d) := by
  rcases hd.eq_or_lt with rfl | hd
  · simp only [add_zero]; linarith
  have hpos : 0 < b + d - a := by linarith
  set θ := d / (b + d - a) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg hd.le hpos.le
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hpos]; linarith
  have hθeq : θ * (b + d - a) = d := by rw [hθ]; field_simp
  have hA : θ • a + (1 - θ) • (b + d) = b := by
    simp only [smul_eq_mul]; linear_combination (-1 : ℝ) * hθeq
  have hB : (1 - θ) • a + θ • (b + d) = a + d := by
    simp only [smul_eq_mul]; linear_combination hθeq
  have h1 := hc.concave.2 (mem_Ici.2 ha) (mem_Ici.2 (by linarith : (0:ℝ) ≤ b + d)) hθ0
    (by linarith : (0:ℝ) ≤ 1 - θ) (by ring)
  have h2 := hc.concave.2 (mem_Ici.2 ha) (mem_Ici.2 (by linarith : (0:ℝ) ≤ b + d))
    (by linarith : (0:ℝ) ≤ 1 - θ) hθ0 (by ring)
  rw [hA] at h1
  rw [hB] at h2
  simp only [smul_eq_mul] at h1 h2
  linarith

/-- `c` is subadditive on `[0,∞)`. -/
theorem subadd (hc : IsOrderingCost c c0 K0 cInf KInf) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    c (a + b) ≤ c a + c b := by
  have := incr_anti hc (le_refl (0:ℝ)) ha hb
  rw [hc.zero, zero_add] at this
  linarith

theorem slope_le_c0 (hc : IsOrderingCost c c0 K0 cInf KInf) {k : ℝ} (hk : k ∈ slopeSet c) :
    k ≤ c0 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨K, _, z, hz, hkz⟩ := hk
  have hU : {p : ℝ × ℝ | p.1 < k} ∈ 𝓝 ((c0, K0) : ℝ × ℝ) :=
    IsOpen.mem_nhds (isOpen_lt continuous_fst continuous_const) hlt
  obtain ⟨z', hsub, hz'⟩ := ((hc.lim_zero _ hU).and (Ioo_mem_nhdsGT hz)).exists
  obtain ⟨k', K', h'⟩ := C2_nonempty hc hz'.1
  have e1 : k' < k := hsub h'
  have e2 := C1_slope_anti hz'.1.le hz'.2 h'.1 hkz.1
  simp only at e2
  linarith

theorem cInf_le_slope (hc : IsOrderingCost c c0 K0 cInf KInf) {k : ℝ} (hk : k ∈ slopeSet c) :
    cInf ≤ k := by
  by_contra hlt
  push Not at hlt
  obtain ⟨K, _, z, hz, hkz⟩ := hk
  have hU : {p : ℝ × ℝ | k < p.1} ∈ 𝓝 ((cInf, KInf) : ℝ × ℝ) :=
    IsOpen.mem_nhds (isOpen_lt continuous_const continuous_fst) hlt
  obtain ⟨z', hsub, hz'⟩ := ((hc.lim_top _ hU).and (eventually_gt_atTop z)).exists
  obtain ⟨k', K', h'⟩ := C2_nonempty hc (hz.trans hz')
  have e1 : k < k' := hsub h'
  have e2 := C1_slope_anti hz.le hz' hkz.1 h'.1
  simp only at e2
  linarith

theorem one_mem_slopeSet (hc : IsOrderingCost c c0 K0 cInf KInf) :
    ∃ k, k ∈ slopeSet c := by
  obtain ⟨k, hk, _⟩ := exists_slope hc (zero_lt_one' ℝ)
  exact ⟨k, hk⟩

theorem c0_nonneg (hc : IsOrderingCost c c0 K0 cInf KInf) : 0 ≤ c0 := by
  obtain ⟨k, hk⟩ := one_mem_slopeSet hc
  exact (slope_nonneg hc hk).trans (slope_le_c0 hc hk)

theorem cInf_nonneg (hc : IsOrderingCost c c0 K0 cInf KInf) : 0 ≤ cInf := by
  by_contra hlt
  push Not at hlt
  have hU : {p : ℝ × ℝ | p.1 < 0} ∈ 𝓝 ((cInf, KInf) : ℝ × ℝ) :=
    IsOpen.mem_nhds (isOpen_lt continuous_fst continuous_const) hlt
  obtain ⟨z', hsub, hz'⟩ := ((hc.lim_top _ hU).and (eventually_gt_atTop (0:ℝ))).exists
  obtain ⟨k', K', h'⟩ := C2_nonempty hc hz'
  have e1 : k' < 0 := hsub h'
  have e2 := slope_nonneg hc ⟨K', C1_K_nonneg hc.zero h'.1, z', hz', h'⟩
  linarith

theorem cInf_le_c0 (hc : IsOrderingCost c c0 K0 cInf KInf) : cInf ≤ c0 := by
  obtain ⟨k, hk⟩ := one_mem_slopeSet hc
  exact (cInf_le_slope hc hk).trans (slope_le_c0 hc hk)

/-- `c z ≥ c_∞ z` on `[0,∞)`. -/
theorem cInf_mul_le (hc : IsOrderingCost c c0 K0 cInf KInf) {z : ℝ} (hz : 0 ≤ z) :
    cInf * z ≤ c z := by
  rcases hz.eq_or_lt with rfl | hz
  · rw [hc.zero, mul_zero]
  obtain ⟨k, hk, hck⟩ := exists_slope hc hz
  have e1 := cInf_le_slope hc hk
  have e2 := Kc_nonneg hk
  rw [hck]
  nlinarith

/-- `c d ≤ c_∞ d + K_∞` on `[0,∞)` (the limit line at infinity supports `c`). -/
theorem le_cInf_line (hc : IsOrderingCost c c0 K0 cInf KInf) {d : ℝ} (hd : 0 ≤ d) :
    c d ≤ cInf * d + KInf := by
  by_contra hlt
  push Not at hlt
  have hU : {p : ℝ × ℝ | p.1 * d + p.2 < c d} ∈ 𝓝 ((cInf, KInf) : ℝ × ℝ) :=
    IsOpen.mem_nhds (isOpen_lt ((continuous_fst.mul continuous_const).add continuous_snd)
      continuous_const) hlt
  obtain ⟨z', hsub, hz'⟩ := ((hc.lim_top _ hU).and (eventually_gt_atTop (0:ℝ))).exists
  obtain ⟨k', K', h'⟩ := C2_nonempty hc hz'
  have e1 : k' * d + K' < c d := hsub h'
  have e2 := h'.1.2 d hd
  simp only at e2
  linarith

/-- `c d ≤ c₀ d + K₀` on `[0,∞)` (the limit line at `0+` supports `c`). -/
theorem le_c0_line (hc : IsOrderingCost c c0 K0 cInf KInf) {d : ℝ} (hd : 0 ≤ d) :
    c d ≤ c0 * d + K0 := by
  by_contra hlt
  push Not at hlt
  have hU : {p : ℝ × ℝ | p.1 * d + p.2 < c d} ∈ 𝓝 ((c0, K0) : ℝ × ℝ) :=
    IsOpen.mem_nhds (isOpen_lt ((continuous_fst.mul continuous_const).add continuous_snd)
      continuous_const) hlt
  obtain ⟨z', hsub, hz'⟩ := ((hc.lim_zero _ hU).and self_mem_nhdsWithin).exists
  obtain ⟨k', K', h'⟩ := C2_nonempty hc (mem_Ioi.1 hz')
  have e1 : k' * d + K' < c d := hsub h'
  have e2 := h'.1.2 d hd
  simp only at e2
  linarith

theorem continuousOn_Ioi (hc : IsOrderingCost c c0 K0 cInf KInf) : ContinuousOn c (Ioi 0) := by
  have := hc.concave.continuousOn_interior
  rwa [interior_Ici] at this

/-- `c` is lower semicontinuous at `0` within `[0,∞)` (NB: `c` is unconstrained on `(-∞,0)`,
so plain `LowerSemicontinuousAt c 0` is not derivable). -/
theorem lscWithin_zero (hc : IsOrderingCost c c0 K0 cInf KInf) :
    LowerSemicontinuousWithinAt c (Ici 0) 0 := by
  intro y hy
  rw [hc.zero] at hy
  filter_upwards [self_mem_nhdsWithin] with e he
  exact lt_of_lt_of_le hy (c_nonneg hc he)

/-- The cost of ordering up from `x` to `y`, extended by `c 0 = 0` below `x`, is lower
semicontinuous on all of `ℝ`. -/
theorem lsc_cost_from (hc : IsOrderingCost c c0 K0 cInf KInf) (x : ℝ) :
    LowerSemicontinuous (fun y => c (max (y - x) 0)) := by
  intro y
  rcases le_or_gt (y - x) 0 with hd | hd
  · intro v hv
    simp only [max_eq_right hd, hc.zero] at hv
    exact Eventually.of_forall (fun e => lt_of_lt_of_le hv (c_nonneg hc (le_max_right _ _)))
  · apply ContinuousAt.lowerSemicontinuousAt
    have hcd : ContinuousAt c (max (y - x) 0) := by
      rw [max_eq_left hd.le]
      exact (continuousOn_Ioi hc).continuousAt (Ioi_mem_nhds hd)
    exact ContinuousAt.comp (f := fun y => max (y - x) 0) hcd
      ((continuous_id.sub continuous_const).max continuous_const).continuousAt

end Cost

/-! ## S1 (b): abstract structural (s,S) lemma (no measure theory)

`YsetH c h x` is `Yset` of `Def_PorteusSS_Model` with `hFn … n` replaced by an arbitrary `h`
(`Yset_eq_YsetH` is `rfl`). `NH c h = {x | x ∈ YsetH c h x}` is the "no order" region. -/

section Structural

variable {c : ℝ → ℝ} {c0 K0 cInf KInf : ℝ}

/-- `Y(x)` for an abstract one-period cost `h`. -/
def YsetH (c h : ℝ → ℝ) (x : ℝ) : Set ℝ :=
  {S | x ≤ S ∧ ∀ y : ℝ, x ≤ y → c (S - x) + h S ≤ c (y - x) + h y}

theorem Yset_eq_YsetH (c m φ f0 : ℝ → ℝ) (α : ℝ) (n : ℕ) (x : ℝ) :
    Yset c m φ f0 α n x = YsetH c (hFn c m φ f0 α n) x := rfl

/-- The no-order region `N = {x | x ∈ Y(x)}`. -/
def NH (c h : ℝ → ℝ) : Set ℝ := {x | x ∈ YsetH c h x}

/-- The generalized (s,S) policy: no order on `[s,∞)`, the largest optimum below `s`.
(Taking `max (Y x)` everywhere fails `IsGenSS` (i) when ties occur on `[s,∞)`.) -/
noncomputable def polH (c h : ℝ → ℝ) (x : ℝ) : ℝ :=
  if sInf (NH c h) ≤ x then x else sSup (YsetH c h x)

/-- The quasi-`K_k`-convexity hypothesis on `G_k = k· + h`, in the "no bad triple" form. -/
def QKHyp (c h : ℝ → ℝ) : Prop :=
  ∀ k ∈ slopeSet c, ∀ x y z : ℝ, x < y → y < z →
    ¬ (k * x + h x < k * y + h y ∧ k * z + h z + Kc c k < k * y + h y)

theorem qk_of_quasiKConvexOn {G : ℝ → ℝ} {K : ℝ} (hG : QuasiKConvexOn G K univ) {x y z : ℝ}
    (hxy : x < y) (hyz : y < z) : ¬ (G x < G y ∧ G z + K < G y) := by
  rintro ⟨h1, h2⟩
  have hxz : 0 < z - x := by linarith
  set l := (z - y) / (z - x) with hl
  have hl0 : 0 ≤ l := div_nonneg (by linarith) hxz.le
  have hl1 : l ≤ 1 := by rw [hl, div_le_one hxz]; linarith
  have hly : l * x + (1 - l) * z = y := by
    rw [hl]; field_simp; ring
  have := hG.2 x (mem_univ _) z (mem_univ _) (by linarith) l hl0 hl1
  rw [hly] at this
  rcases le_max_iff.1 this with h | h <;> linarith

theorem mem_NH_iff (hc : IsOrderingCost c c0 K0 cInf KInf) {h : ℝ → ℝ} {x : ℝ} :
    x ∈ NH c h ↔ ∀ y : ℝ, x ≤ y → h x ≤ c (y - x) + h y := by
  simp only [NH, YsetH, mem_ofPred_eq, sub_self, hc.zero, zero_add, le_refl, true_and]

/-- Every optimal order-up-to level is itself in the no-order region (subadditivity). -/
theorem mem_NH_of_mem_YsetH (hc : IsOrderingCost c c0 K0 cInf KInf) {h : ℝ → ℝ} {x S : ℝ}
    (hS : S ∈ YsetH c h x) : S ∈ NH c h := by
  rw [mem_NH_iff hc]
  intro y hy
  by_contra hlt
  push Not at hlt
  have e1 := hS.2 y (hS.1.trans hy)
  have e2 := subadd hc (sub_nonneg.2 hS.1) (sub_nonneg.2 hy)
  rw [show S - x + (y - S) = y - x by ring] at e2
  linarith

/-- `N` is upward closed (quasi-`K_k`-convexity with `k` the slope at the order size). -/
theorem NH_upward (hc : IsOrderingCost c c0 K0 cInf KInf) {h : ℝ → ℝ} (hqk : QKHyp c h)
    {x x' : ℝ} (hx : x ∈ NH c h) (hxx : x ≤ x') : x' ∈ NH c h := by
  rcases hxx.eq_or_lt with rfl | hlt
  · exact hx
  rw [mem_NH_iff hc]
  intro y' hy'
  by_contra hbad
  push Not at hbad
  rcases hy'.eq_or_lt with rfl | hy'gt
  · rw [sub_self, hc.zero] at hbad; linarith
  obtain ⟨k, hk, hck⟩ := exists_slope hc (sub_pos.2 hy'gt)
  have h1 := (mem_NH_iff hc).1 hx y' (by linarith)
  have h2 := le_supporting hk (show 0 ≤ y' - x by linarith)
  apply hqk k hk x x' y' hlt hy'gt
  constructor <;> nlinarith

/-- Coercivity + lower semicontinuity: `Y(x)` is nonempty, bounded above, and contains its
supremum. -/
theorem YsetH_props (hc : IsOrderingCost c c0 K0 cInf KInf) {h : ℝ → ℝ}
    (hlsc : LowerSemicontinuous h) (hcoer : Tendsto (fun y => cInf * y + h y) atTop atTop)
    (x : ℝ) :
    (YsetH c h x).Nonempty ∧ BddAbove (YsetH c h x) ∧ sSup (YsetH c h x) ∈ YsetH c h x := by
  set F : ℝ → ℝ := fun y => c (max (y - x) 0) + h y with hFdef
  have hF : LowerSemicontinuous F := (lsc_cost_from hc x).add hlsc
  have hFeq : ∀ y, x ≤ y → F y = c (y - x) + h y := by
    intro y hy
    simp only [hFdef, max_eq_left (sub_nonneg.2 hy)]
  have hcoerF : Tendsto F atTop atTop := by
    have h1 : Tendsto (fun y => cInf * y + h y + (-(cInf * x))) atTop atTop :=
      tendsto_atTop_add_const_right _ _ hcoer
    refine tendsto_atTop_mono' atTop ?_ h1
    filter_upwards [eventually_ge_atTop x] with y hy
    rw [hFeq y hy]
    have := cInf_mul_le hc (sub_nonneg.2 hy)
    nlinarith
  obtain ⟨R, hR⟩ := eventually_atTop.1 (hcoerF.eventually_gt_atTop (F x))
  set R' := max R x with hR'
  have hxmem : x ∈ Icc x R' := ⟨le_rfl, le_max_right _ _⟩
  obtain ⟨a, ha, hmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn ⟨x, hxmem⟩ isCompact_Icc (hF.lowerSemicontinuousOn _)
  have hamin : ∀ y, x ≤ y → F a ≤ F y := by
    intro y hy
    by_cases hyR : y ≤ R'
    · exact hmin ⟨hy, hyR⟩
    · push Not at hyR
      have e1 := hR y (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hyR))
      have e2 : F a ≤ F x := hmin hxmem
      linarith
  have hYeq : YsetH c h x = Ici x ∩ F ⁻¹' Iic (F a) := by
    ext S
    simp only [YsetH, mem_ofPred_eq, mem_inter_iff, mem_Ici, mem_preimage, mem_Iic]
    constructor
    · rintro ⟨hxS, hS⟩
      refine ⟨hxS, ?_⟩
      have := hS a ha.1
      rw [hFeq S hxS, hFeq a ha.1]
      exact this
    · rintro ⟨hxS, hS⟩
      refine ⟨hxS, fun y hy => ?_⟩
      rw [← hFeq S hxS, ← hFeq y hy]
      exact hS.trans (hamin y hy)
  have hamem : a ∈ YsetH c h x := by
    rw [hYeq]; exact ⟨ha.1, (le_rfl : F a ≤ F a)⟩
  have hbdd : BddAbove (YsetH c h x) := by
    refine ⟨R', fun S hS => ?_⟩
    rw [hYeq] at hS
    by_contra hSR
    push Not at hSR
    have e1 := hR S (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hSR))
    have e2 : F a ≤ F x := hmin hxmem
    have e3 : F S ≤ F a := hS.2
    linarith
  have hclosed : IsClosed (YsetH c h x) := by
    rw [hYeq]; exact isClosed_Ici.inter (hF.isClosed_preimage (F a))
  exact ⟨⟨a, hamem⟩, hbdd, hclosed.csSup_mem ⟨a, hamem⟩ hbdd⟩

/-- A2-type hypothesis: if `c₀ x + h x → ∞` as `x → -∞`, ordering is strictly better somewhere. -/
theorem exists_not_NH_of_tendsto (hc : IsOrderingCost c c0 K0 cInf KInf) {h : ℝ → ℝ}
    (hbot : Tendsto (fun x => c0 * x + h x) atBot atTop) :
    ∃ x₀ y₀ : ℝ, x₀ ≤ y₀ ∧ c (y₀ - x₀) + h y₀ < h x₀ := by
  obtain ⟨x, hx1, hx2⟩ :=
    ((hbot.eventually_gt_atTop (h 0 + K0)).and (eventually_le_atBot (0:ℝ))).exists
  refine ⟨x, 0, hx2, ?_⟩
  have := le_c0_line hc (show 0 ≤ 0 - x by linarith)
  nlinarith

/-- `N = [s, ∞)` with `s = sInf N`. -/
theorem NH_eq_Ici (hc : IsOrderingCost c c0 K0 cInf KInf) {h : ℝ → ℝ}
    (hlsc : LowerSemicontinuous h) (hcoer : Tendsto (fun y => cInf * y + h y) atTop atTop)
    (hqk : QKHyp c h) (hne : ∃ x₀ y₀ : ℝ, x₀ ≤ y₀ ∧ c (y₀ - x₀) + h y₀ < h x₀) :
    NH c h = Ici (sInf (NH c h)) := by
  obtain ⟨x₀, y₀, hxy₀, hlt₀⟩ := hne
  have hx₀ : x₀ ∉ NH c h := by
    rw [mem_NH_iff hc]; intro H; have := H y₀ hxy₀; linarith
  have hbdd : BddBelow (NH c h) := by
    refine ⟨x₀, fun x hx => ?_⟩
    by_contra hlt
    push Not at hlt
    exact hx₀ (NH_upward hc hqk hx hlt.le)
  have hNne : (NH c h).Nonempty := by
    obtain ⟨-, -, hmem⟩ := YsetH_props hc hlsc hcoer x₀
    exact ⟨_, mem_NH_of_mem_YsetH hc hmem⟩
  set s := sInf (NH c h) with hs
  have hgt : ∀ x, s < x → x ∈ NH c h := by
    intro x hx
    obtain ⟨n, hn, hnx⟩ := exists_lt_of_csInf_lt hNne hx
    exact NH_upward hc hqk hn hnx.le
  have hsmem : s ∈ NH c h := by
    rw [mem_NH_iff hc]
    intro y hy
    rcases hy.eq_or_lt with rfl | hsy
    · rw [sub_self, hc.zero, zero_add]
    by_contra hbad
    push Not at hbad
    set mid := (c (y - s) + h y + h s) / 2 with hmid
    have e1 : ∀ᶠ x' in 𝓝 s, mid < h x' := hlsc s mid (by rw [hmid]; linarith)
    have hcont : ContinuousAt (fun x' => c (y - x') + h y) s := by
      have hcy : ContinuousAt c (y - s) :=
        (continuousOn_Ioi hc).continuousAt (Ioi_mem_nhds (sub_pos.2 hsy))
      exact (ContinuousAt.comp (f := fun x' => y - x') hcy
        (continuous_const.sub continuous_id).continuousAt).add continuousAt_const
    have e2 : ∀ᶠ x' in 𝓝 s, c (y - x') + h y < mid :=
      hcont.eventually (eventually_lt_nhds (by rw [hmid]; linarith))
    have e3 : ∀ᶠ x' in 𝓝 s, x' < y := Iio_mem_nhds hsy
    have e4 : ∀ᶠ x' in 𝓝[>] s, (mid < h x' ∧ c (y - x') + h y < mid) ∧ x' < y :=
      nhdsWithin_le_nhds ((e1.and e2).and e3)
    obtain ⟨x', ⟨⟨h1, h2⟩, h3⟩, h4⟩ :=
      (e4.and (self_mem_nhdsWithin : Ioi s ∈ 𝓝[>] s)).exists
    have := (mem_NH_iff hc).1 (hgt x' h4) y h3.le
    linarith
  ext x
  constructor
  · intro hx; exact csInf_le hbdd hx
  · intro hx
    rcases (mem_Ici.1 hx).eq_or_lt with rfl | hlt
    · exact hsmem
    · exact hgt x hlt

/-- The largest optimum is antitone below `s` (concavity exchange argument). -/
theorem sSup_YsetH_anti (hc : IsOrderingCost c c0 K0 cInf KInf) {h : ℝ → ℝ}
    (hlsc : LowerSemicontinuous h) (hcoer : Tendsto (fun y => cInf * y + h y) atTop atTop)
    (hqk : QKHyp c h) (hne : ∃ x₀ y₀ : ℝ, x₀ ≤ y₀ ∧ c (y₀ - x₀) + h y₀ < h x₀)
    {z x : ℝ} (hzx : z < x) (hxs : x < sInf (NH c h)) :
    sSup (YsetH c h x) ≤ sSup (YsetH c h z) := by
  have hN := NH_eq_Ici hc hlsc hcoer hqk hne
  obtain ⟨-, -, hSx⟩ := YsetH_props hc hlsc hcoer x
  obtain ⟨-, hbz, hSz⟩ := YsetH_props hc hlsc hcoer z
  set Sx := sSup (YsetH c h x)
  set Sz := sSup (YsetH c h z)
  have hSxs : sInf (NH c h) ≤ Sx := by
    have := mem_NH_of_mem_YsetH hc hSx; rw [hN] at this; exact this
  have hSzs : sInf (NH c h) ≤ Sz := by
    have := mem_NH_of_mem_YsetH hc hSz; rw [hN] at this; exact this
  by_contra hlt
  push Not at hlt
  have o1 := hSz.2 Sx (by linarith)
  have o2 := hSx.2 Sz (by linarith)
  have cc := incr_anti hc (a := Sz - x) (b := Sx - x) (d := x - z) (by linarith) (by linarith)
    (by linarith)
  rw [show Sx - x + (x - z) = Sx - z by ring, show Sz - x + (x - z) = Sz - z by ring] at cc
  have hmem : Sx ∈ YsetH c h z := by
    refine ⟨by linarith, fun y hy => ?_⟩
    have := hSz.2 y hy
    linarith
  have := le_csSup hbz hmem
  linarith

/-- **Abstract structural (s,S) lemma.** For lower semicontinuous, coercive `h` whose
`G_k = k· + h` are quasi-`K_k`-convex for all `k ∈ C`, and with ordering strictly better
somewhere, `polH` is a generalized `(s,S)` policy with `S = s = sInf N`, and it is optimal. -/
theorem genSS_of_quasiK (hc : IsOrderingCost c c0 K0 cInf KInf) {h : ℝ → ℝ}
    (hlsc : LowerSemicontinuous h) (hcoer : Tendsto (fun y => cInf * y + h y) atTop atTop)
    (hqk : QKHyp c h) (hne : ∃ x₀ y₀ : ℝ, x₀ ≤ y₀ ∧ c (y₀ - x₀) + h y₀ < h x₀) :
    IsGenSS (polH c h) (sInf (NH c h)) (sInf (NH c h)) ∧
      ∀ x : ℝ, polH c h x ∈ YsetH c h x := by
  have hN := NH_eq_Ici hc hlsc hcoer hqk hne
  refine ⟨⟨fun x hx => if_pos hx, fun z x hzx hxs => ?_, le_rfl⟩, fun x => ?_⟩
  · have hz : ¬ sInf (NH c h) ≤ z := by push Not; linarith
    have hx : ¬ sInf (NH c h) ≤ x := by push Not; exact hxs
    simp only [polH, if_neg hz, if_neg hx]
    refine ⟨sSup_YsetH_anti hc hlsc hcoer hqk hne hzx hxs, ?_⟩
    obtain ⟨-, -, hSx⟩ := YsetH_props hc hlsc hcoer x
    have := mem_NH_of_mem_YsetH hc hSx
    rw [hN] at this
    exact this
  · unfold polH
    split_ifs with hx
    · have : x ∈ NH c h := by rw [hN]; exact hx
      exact this
    · exact (YsetH_props hc hlsc hcoer x).2.2

/-- The same, stated for the model's `Yset` (with `h = hFn … n`), in the exact shape of the
leaf's conclusion (b). -/
theorem genSS_model (c m φ f0 : ℝ → ℝ) (α c0 K0 cInf KInf : ℝ) (n : ℕ)
    (hc : IsOrderingCost c c0 K0 cInf KInf)
    (hlsc : LowerSemicontinuous (hFn c m φ f0 α n))
    (hcoer : Tendsto (fun y => cInf * y + hFn c m φ f0 α n y) atTop atTop)
    (hqk : QKHyp c (hFn c m φ f0 α n))
    (hbot : Tendsto (fun x => c0 * x + hFn c m φ f0 α n x) atBot atTop) :
    ∃ s S : ℝ, ∃ pol : ℝ → ℝ, IsGenSS pol s S ∧ ∀ x : ℝ, pol x ∈ Yset c m φ f0 α n x :=
  ⟨_, _, _, genSS_of_quasiK hc hlsc hcoer hqk (exists_not_NH_of_tendsto hc hbot)⟩

end Structural

/-! ## S2: the core lemma — convolution with a TP2 density preserves quasi-K-convexity

Route (resume packet, second pass): split `g = c + A + B + e` (`decomp`); the functionals
`d₁ h = F_h(y) - F_h(x)`, `d₂ h = F_h(y) - F_h(z)` give `α, β, γ, δ, b₁, b₂`; inequality (I)
`β γ ≤ α δ` (`ineq_I`) and (II) `β b₁ ≤ α (K - b₂)` (`ineq_II`) are reduced by the layer cake
(`lc3_nonpos`) to level sets, where (I) is the TP2 inequality for interval masses (`ray_I`) and
(II) is mass balance plus aggregated TP2 (`tp2_agg`, `ray_II`). -/

section Core

open MeasureTheory

/-- Pointwise TP2 of `(x, t) ↦ φ (x - t)`: the `k = 2` determinant condition of `IsPF 2`. -/
def TP2 (φ : ℝ → ℝ) : Prop :=
  ∀ x1 x2 t1 t2 : ℝ, x1 < x2 → t1 < t2 → φ (x1 - t2) * φ (x2 - t1) ≤ φ (x1 - t1) * φ (x2 - t2)

variable {φ : ℝ → ℝ}

theorem tp2_weak (hT : TP2 φ) {x1 x2 t1 t2 : ℝ} (hx : x1 ≤ x2) (ht : t1 ≤ t2) :
    φ (x1 - t2) * φ (x2 - t1) ≤ φ (x1 - t1) * φ (x2 - t2) := by
  rcases hx.lt_or_eq with hx | hx
  · rcases ht.lt_or_eq with ht | ht
    · exact hT _ _ _ _ hx ht
    · subst ht; exact le_rfl
  · subst hx; rw [mul_comm]

/-- `conv h ψ w = ∫ t, h t * ψ (w - t)` (substitution `t = w - ξ`). -/
theorem conv_eq_t (h ψ : ℝ → ℝ) (w : ℝ) : conv h ψ w = ∫ t, h t * ψ (w - t) := by
  have := integral_sub_left_eq_self (fun t => h t * ψ (w - t)) (volume : Measure ℝ) w
  simp only [sub_sub_cancel] at this
  exact this

/-- **Ray case of (I)**: the interval masses of a TP2 function are TP2 under translation. -/
theorem ray_I (hφi : Integrable φ) (hT : TP2 φ) {x y z a b : ℝ} (hxy : x ≤ y) (hyz : y ≤ z)
    (hab : a ≤ b) :
    (∫ u in (y - a)..(z - a), φ u) * (∫ u in (x - b)..(y - b), φ u) ≤
      (∫ u in (x - a)..(y - a), φ u) * (∫ u in (y - b)..(z - b), φ u) := by
  have e1 : (∫ u in (y - a)..(z - a), φ u) = ∫ v in y..z, φ (v - a) :=
    (intervalIntegral.integral_comp_sub_right φ a).symm
  have e2 : (∫ u in (x - b)..(y - b), φ u) = ∫ u in x..y, φ (u - b) :=
    (intervalIntegral.integral_comp_sub_right φ b).symm
  have e3 : (∫ u in (x - a)..(y - a), φ u) = ∫ u in x..y, φ (u - a) :=
    (intervalIntegral.integral_comp_sub_right φ a).symm
  have e4 : (∫ u in (y - b)..(z - b), φ u) = ∫ v in y..z, φ (v - b) :=
    (intervalIntegral.integral_comp_sub_right φ b).symm
  rw [e1, e2, e3, e4]
  have hi : ∀ (s p q : ℝ), IntervalIntegrable (fun u => φ (u - s)) volume p q :=
    fun s p q => (hφi.comp_sub_right s).intervalIntegrable
  have l1 : (∫ v in y..z, φ (v - a)) * (∫ u in x..y, φ (u - b)) =
      ∫ u in x..y, (∫ v in y..z, φ (v - a)) * φ (u - b) :=
    (intervalIntegral.integral_const_mul _ _).symm
  have l2 : (∫ u in x..y, φ (u - a)) * (∫ v in y..z, φ (v - b)) =
      ∫ u in x..y, φ (u - a) * (∫ v in y..z, φ (v - b)) :=
    (intervalIntegral.integral_mul_const _ _).symm
  rw [l1, l2]
  apply intervalIntegral.integral_mono_on hxy ((hi b x y).const_mul _) ((hi a x y).mul_const _)
  intro u hu
  have m1 : (∫ v in y..z, φ (v - a)) * φ (u - b) = ∫ v in y..z, φ (v - a) * φ (u - b) :=
    (intervalIntegral.integral_mul_const _ _).symm
  have m2 : φ (u - a) * (∫ v in y..z, φ (v - b)) = ∫ v in y..z, φ (u - a) * φ (v - b) :=
    (intervalIntegral.integral_const_mul _ _).symm
  rw [m1, m2]
  apply intervalIntegral.integral_mono_on hyz ((hi a y z).mul_const _) ((hi b y z).const_mul _)
  intro v hv
  have := tp2_weak hT (x1 := u) (x2 := v) (by linarith [hu.2, hv.1]) hab
  linarith

theorem integrable_ind_mul (hφi : Integrable φ) {S : Set ℝ} (hS : MeasurableSet S) (w : ℝ) :
    Integrable (fun t => S.indicator 1 t * φ (w - t)) := by
  have : (fun t => S.indicator 1 t * φ (w - t)) = S.indicator (fun t => φ (w - t)) := by
    funext t; by_cases ht : t ∈ S <;> simp [ht]
  rw [this]; exact (hφi.comp_sub_left w).indicator hS

/-- **Aggregated TP2**: a lower set `L` against a nonnegative weight living on `Lᶜ`. -/
theorem tp2_agg (hφi : Integrable φ) (hT : TP2 φ) {L : Set ℝ} (hL : IsLowerSet L)
    (hLm : MeasurableSet L) {W : ℝ → ℝ} (hW0 : ∀ t, 0 ≤ W t) (hWL : ∀ t ∈ L, W t = 0)
    (hWi : ∀ w, Integrable (fun t => W t * φ (w - t))) {x y : ℝ} (hxy : x ≤ y) :
    (∫ t, L.indicator 1 t * φ (y - t)) * (∫ t, W t * φ (x - t)) ≤
      (∫ t, L.indicator 1 t * φ (x - t)) * (∫ t, W t * φ (y - t)) := by
  rw [← integral_mul_const, ← integral_mul_const]
  apply integral_mono ((integrable_ind_mul hφi hLm y).mul_const _)
    ((integrable_ind_mul hφi hLm x).mul_const _)
  intro s
  by_cases hs : s ∈ L
  · simp only [Set.indicator_of_mem hs, Pi.one_apply, one_mul]
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_mono ((hWi x).const_mul _) ((hWi y).const_mul _)
    intro t
    by_cases ht : t ∈ L
    · simp [hWL t ht]
    · have hst : s ≤ t := by
        by_contra h
        push Not at h
        exact ht (hL h.le hs)
      have := mul_le_mul_of_nonneg_left (tp2_weak hT hxy hst) (hW0 t)
      nlinarith
  · simp [Set.indicator_of_notMem hs]

theorem integrable_ind_conv (hφi : Integrable φ) {S : Set ℝ} (hS : MeasurableSet S) (w : ℝ) :
    Integrable (fun ξ => S.indicator 1 (w - ξ) * φ ξ) := by
  refine hφi.bdd_mul (c := 1) ?_ (ae_of_all _ fun ξ => ?_)
  · exact ((measurable_one.indicator hS).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  · by_cases h : w - ξ ∈ S <;> simp [h]

theorem conv_ind_anti (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ) {L : Set ℝ} (hL : IsLowerSet L)
    (hLm : MeasurableSet L) {w w' : ℝ} (hww : w ≤ w') :
    conv (L.indicator 1) φ w' ≤ conv (L.indicator 1) φ w := by
  unfold conv
  apply integral_mono (integrable_ind_conv hφi hLm w') (integrable_ind_conv hφi hLm w)
  intro ξ
  by_cases h : w' - ξ ∈ L
  · have h' : w - ξ ∈ L := hL (by linarith) h
    simp [h, h']
  · simp only [Set.indicator_of_notMem h, zero_mul]
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (hφ0 ξ)

theorem conv_ind_mono (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ) {V : Set ℝ} (hV : IsUpperSet V)
    (hVm : MeasurableSet V) {w w' : ℝ} (hww : w ≤ w') :
    conv (V.indicator 1) φ w ≤ conv (V.indicator 1) φ w' := by
  unfold conv
  apply integral_mono (integrable_ind_conv hφi hVm w) (integrable_ind_conv hφi hVm w')
  intro ξ
  by_cases h : w - ξ ∈ V
  · have h' : w' - ξ ∈ V := hV (by linarith) h
    simp [h, h']
  · simp only [Set.indicator_of_notMem h, zero_mul]
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (hφ0 ξ)

theorem conv_nonneg (hφ0 : ∀ t, 0 ≤ φ t) {h : ℝ → ℝ} (h0 : ∀ t, 0 ≤ h t) (w : ℝ) :
    0 ≤ conv h φ w :=
  integral_nonneg fun ξ => mul_nonneg (h0 _) (hφ0 ξ)

/-- **Ray case of (II)**: a lower set `L` against a `[0,K]`-valued `e` vanishing on `L`. -/
theorem ray_II (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ) (hφ1 : ∫ t, φ t = 1) (hT : TP2 φ)
    {L : Set ℝ} (hL : IsLowerSet L) (hLm : MeasurableSet L) {e : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (he0 : ∀ t, 0 ≤ e t) (heK : ∀ t, e t ≤ K) (heL : ∀ t ∈ L, e t = 0) (hem : Measurable e)
    {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) :
    (conv (L.indicator 1) φ y - conv (L.indicator 1) φ z) * (conv e φ y - conv e φ x) ≤
      (conv (L.indicator 1) φ x - conv (L.indicator 1) φ y) * (K - (conv e φ y - conv e φ z)) := by
  have hshift : ∀ w, ∫ t, φ (w - t) = 1 := fun w => by
    rw [integral_sub_left_eq_self φ volume w]; exact hφ1
  set W : ℝ → ℝ := fun t => K - e t - K * L.indicator 1 t with hWdef
  have hW0 : ∀ t, 0 ≤ W t := by
    intro t
    by_cases ht : t ∈ L
    · simp [hWdef, ht, heL t ht]
    · simp only [hWdef, Set.indicator_of_notMem ht, mul_zero, sub_zero]
      linarith [heK t]
  have hWK : ∀ t, W t ≤ K := by
    intro t
    by_cases ht : t ∈ L
    · simp [hWdef, ht, heL t ht, hK]
    · simp only [hWdef, Set.indicator_of_notMem ht, mul_zero, sub_zero]
      linarith [he0 t]
  have hWL : ∀ t ∈ L, W t = 0 := by intro t ht; simp [hWdef, ht, heL t ht]
  have hWm : Measurable W :=
    (measurable_const.sub hem).sub (measurable_const.mul (measurable_one.indicator hLm))
  have hWi : ∀ w, Integrable (fun t => W t * φ (w - t)) := fun w =>
    (hφi.comp_sub_left w).bdd_mul (c := K) hWm.aestronglyMeasurable (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hW0 t)]; exact hWK t)
  have hEi : ∀ w, Integrable (fun t => e t * φ (w - t)) := fun w =>
    (hφi.comp_sub_left w).bdd_mul (c := K) hem.aestronglyMeasurable (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (he0 t)]; exact heK t)
  have hm : ∀ w, ∫ t, W t * φ (w - t) = K - conv e φ w - K * conv (L.indicator 1) φ w := by
    intro w
    rw [conv_eq_t, conv_eq_t]
    have : (fun t => W t * φ (w - t)) = fun t =>
        K * φ (w - t) - e t * φ (w - t) - K * (L.indicator 1 t * φ (w - t)) := by
      funext t; simp only [hWdef]; ring
    have i1 : Integrable (fun t => K * φ (w - t) - e t * φ (w - t)) :=
      ((hφi.comp_sub_left w).const_mul K).sub (hEi w)
    rw [this, integral_sub i1 ((integrable_ind_mul hφi hLm w).const_mul K),
      integral_sub ((hφi.comp_sub_left w).const_mul K) (hEi w), integral_const_mul,
      integral_const_mul, hshift]
    ring
  have hTT := tp2_agg hφi hT hL hLm hW0 hWL hWi hxy
  rw [hm, hm, ← conv_eq_t, ← conv_eq_t] at hTT
  have hmx0 : 0 ≤ K - conv e φ x - K * conv (L.indicator 1) φ x := by
    rw [← hm]; exact integral_nonneg fun t => mul_nonneg (hW0 t) (hφ0 _)
  have hmy0 : 0 ≤ K - conv e φ y - K * conv (L.indicator 1) φ y := by
    rw [← hm]; exact integral_nonneg fun t => mul_nonneg (hW0 t) (hφ0 _)
  have hpxy := conv_ind_anti hφ0 hφi hL hLm hxy
  have hpyz := conv_ind_anti hφ0 hφi hL hLm hyz
  have hpz := conv_nonneg hφ0 (Set.indicator_nonneg (fun _ _ => zero_le_one) : ∀ t, 0 ≤ L.indicator (1 : ℝ → ℝ) t) z
  have hEz := conv_nonneg hφ0 he0 z
  set px := conv (L.indicator 1) φ x
  set py := conv (L.indicator 1) φ y
  set pz := conv (L.indicator 1) φ z
  set Ex := conv e φ x
  set Ey := conv e φ y
  set Ez := conv e φ z
  set mx := K - Ex - K * px with hmx
  set my := K - Ey - K * py with hmy
  have key : 0 ≤ (px - pz) * my - (py - pz) * mx := by
    rcases le_total my mx with h | h
    · nlinarith [mul_le_mul_of_nonneg_left h hpz]
    · nlinarith [mul_nonneg (sub_nonneg.2 hpxy) hmy0, mul_nonneg (sub_nonneg.2 hpyz) (sub_nonneg.2 h)]
  nlinarith [mul_nonneg (mul_nonneg hK (sub_nonneg.2 hpxy)) hpz, mul_nonneg (sub_nonneg.2 hpxy) hEz]

/-- `conv` of an indicator is the `φ`-mass of the reflected, translated set. -/
theorem conv_indicator {S : Set ℝ} (hS : MeasurableSet S) (w : ℝ) :
    conv (S.indicator 1) φ w = ∫ ξ in {ξ | w - ξ ∈ S}, φ ξ := by
  unfold conv
  have hS' : MeasurableSet {ξ : ℝ | w - ξ ∈ S} :=
    hS.preimage (measurable_const.sub measurable_id)
  rw [← integral_indicator hS']
  congr 1
  funext ξ
  by_cases h : w - ξ ∈ S <;> simp [h]

/-- **Layer cake** against the density `φ`, with integrability of the layer masses. -/
theorem layer_cake (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ) {h : ℝ → ℝ} (hh0 : ∀ t, 0 ≤ h t)
    (hhm : Measurable h) (hhi : Integrable (fun ξ => h ξ * φ ξ)) :
    IntegrableOn (fun l => ∫ ξ in {ξ | l < h ξ}, φ ξ) (Ioi 0) ∧
      ∫ ξ, h ξ * φ ξ = ∫ l in Ioi 0, ∫ ξ in {ξ | l < h ξ}, φ ξ := by
  set μ : Measure ℝ := volume.withDensity (fun ξ => ENNReal.ofReal (φ ξ)) with hμ
  have hd : AEMeasurable (fun ξ => ENNReal.ofReal (φ ξ)) volume :=
    hφi.aemeasurable.ennreal_ofReal
  have hfin : ∀ᵐ ξ ∂(volume : Measure ℝ), ENNReal.ofReal (φ ξ) < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hsm : ∀ ξ, (ENNReal.ofReal (φ ξ)).toReal • h ξ = h ξ * φ ξ := fun ξ => by
    rw [ENNReal.toReal_ofReal (hφ0 ξ), smul_eq_mul, mul_comm]
  have hint : Integrable h μ := by
    rw [hμ, integrable_withDensity_iff_integrable_smul₀' hd hfin]
    simp only [hsm]
    exact hhi
  have hlhs : ∫ ξ, h ξ ∂μ = ∫ ξ, h ξ * φ ξ := by
    rw [hμ, integral_withDensity_eq_integral_toReal_smul₀ hd hfin]
    simp only [hsm]
  have hmeas : ∀ l : ℝ, μ.real {ξ | l < h ξ} = ∫ ξ in {ξ | l < h ξ}, φ ξ := by
    intro l
    have hS : MeasurableSet {ξ | l < h ξ} := measurableSet_lt measurable_const hhm
    rw [measureReal_def, hμ, withDensity_apply _ hS,
      ← ofReal_integral_eq_lintegral_ofReal hφi.integrableOn (ae_of_all _ hφ0),
      ENNReal.toReal_ofReal (setIntegral_nonneg hS fun ξ _ => hφ0 ξ)]
  have key := hint.integral_eq_integral_meas_lt (ae_of_all _ hh0)
  simp only [hmeas] at key
  refine ⟨?_, by rw [← hlhs, key]⟩
  have hlint := lintegral_eq_lintegral_meas_lt μ (ae_of_all _ hh0) hint.aemeasurable
  have hne : ∫⁻ l in Ioi 0, μ {ξ | l < h ξ} ≠ ⊤ := by
    rw [← hlint]; exact hint.lintegral_lt_top.ne
  have hanti : Antitone (fun l : ℝ => μ {ξ | l < h ξ}) := fun s t hst =>
    measure_mono fun ξ hx => lt_of_le_of_lt hst hx
  have hI := integrable_toReal_of_lintegral_ne_top hanti.measurable.aemeasurable hne
  refine hI.congr (ae_of_all _ fun l => ?_)
  simp only
  rw [← measureReal_def, hmeas]

/-- **Layer-cake reduction** of a three-point linear functional to the level sets. -/
theorem lc3_nonpos (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ) {f : ℝ → ℝ} (hf0 : ∀ t, 0 ≤ f t)
    (hfm : Measurable f) (hfi : ∀ w, Integrable (fun ξ => f (w - ξ) * φ ξ)) (x y z c1 c2 c3 : ℝ)
    (h : ∀ l : ℝ, 0 < l → c1 * conv ({t | l < f t}.indicator 1) φ x +
      c2 * conv ({t | l < f t}.indicator 1) φ y + c3 * conv ({t | l < f t}.indicator 1) φ z ≤ 0) :
    c1 * conv f φ x + c2 * conv f φ y + c3 * conv f φ z ≤ 0 := by
  have hc : ∀ w, IntegrableOn (fun l => conv ({t | l < f t}.indicator 1) φ w) (Ioi 0) ∧
      conv f φ w = ∫ l in Ioi 0, conv ({t | l < f t}.indicator 1) φ w := by
    intro w
    have hm : Measurable (fun ξ => f (w - ξ)) := hfm.comp (measurable_const.sub measurable_id)
    obtain ⟨h1, h2⟩ := layer_cake hφ0 hφi (fun ξ => hf0 (w - ξ)) hm (hfi w)
    have hset : ∀ l : ℝ, conv ({t | l < f t}.indicator 1) φ w = ∫ ξ in {ξ | l < f (w - ξ)}, φ ξ :=
      fun l => conv_indicator (measurableSet_lt measurable_const hfm) w
    simp only [hset]
    exact ⟨h1, h2⟩
  obtain ⟨ix, ex⟩ := hc x
  obtain ⟨iy, ey⟩ := hc y
  obtain ⟨iz, ez⟩ := hc z
  have hsum : ∫ l in Ioi 0, (c1 * conv ({t | l < f t}.indicator 1) φ x +
      c2 * conv ({t | l < f t}.indicator 1) φ y + c3 * conv ({t | l < f t}.indicator 1) φ z) =
      c1 * conv f φ x + c2 * conv f φ y + c3 * conv f φ z := by
    have i1 : Integrable (fun l => c1 * conv ({t | l < f t}.indicator 1) φ x)
        (volume.restrict (Ioi 0)) := ix.const_mul c1
    have i2 : Integrable (fun l => c2 * conv ({t | l < f t}.indicator 1) φ y)
        (volume.restrict (Ioi 0)) := iy.const_mul c2
    have i3 : Integrable (fun l => c3 * conv ({t | l < f t}.indicator 1) φ z)
        (volume.restrict (Ioi 0)) := iz.const_mul c3
    have i12 : Integrable (fun l => c1 * conv ({t | l < f t}.indicator 1) φ x +
        c2 * conv ({t | l < f t}.indicator 1) φ y) (volume.restrict (Ioi 0)) := i1.add i2
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
      integral_const_mul, ← ex, ← ey, ← ez]
  rw [← hsum]
  exact setIntegral_nonpos measurableSet_Ioi fun l hl => h l hl

/-- A set squeezed between `Iio a` and `Iic a`: `conv` of its indicator is a tail mass. -/
theorem conv_ind_lower (hφi : Integrable φ) {L : Set ℝ} {a : ℝ} (h1 : Iio a ⊆ L)
    (h2 : L ⊆ Iic a) (hLm : MeasurableSet L) (w : ℝ) :
    conv (L.indicator 1) φ w = (∫ ξ, φ ξ) - ∫ ξ in Iic (w - a), φ ξ := by
  rw [conv_indicator hLm]
  have hS : {ξ | w - ξ ∈ L} =ᵐ[volume] Ioi (w - a) := by
    have hsub1 : {ξ | w - ξ ∈ L} ⊆ Ici (w - a) := fun ξ hξ => by
      have := h2 hξ
      simp only [mem_Iic] at this
      simp only [mem_Ici]
      linarith
    have hsub2 : Ioi (w - a) ⊆ {ξ | w - ξ ∈ L} := fun ξ hξ => h1 (by
      simp only [mem_Ioi] at hξ
      simp only [mem_Iio]
      linarith)
    apply EventuallyLE.antisymm
    · exact (ae_le_set.2 (by rw [sdiff_eq_empty.2 hsub1, measure_empty])).trans
        Ioi_ae_eq_Ici.symm.le
    · exact ae_le_set.2 (by rw [sdiff_eq_empty.2 hsub2, measure_empty])
  rw [setIntegral_congr_set hS]
  have := integral_add_compl (measurableSet_Iic (a := w - a)) hφi
  rw [compl_Iic] at this
  linarith

/-- A set squeezed between `Ioi b` and `Ici b`: `conv` of its indicator is a CDF value. -/
theorem conv_ind_upper {V : Set ℝ} {b : ℝ} (h1 : Ioi b ⊆ V) (h2 : V ⊆ Ici b)
    (hVm : MeasurableSet V) (w : ℝ) :
    conv (V.indicator 1) φ w = ∫ ξ in Iic (w - b), φ ξ := by
  rw [conv_indicator hVm]
  have hS : {ξ | w - ξ ∈ V} =ᵐ[volume] Iic (w - b) := by
    have hsub1 : {ξ | w - ξ ∈ V} ⊆ Iic (w - b) := fun ξ hξ => by
      have := h2 hξ
      simp only [mem_Ici] at this
      simp only [mem_Iic]
      linarith
    have hsub2 : Iio (w - b) ⊆ {ξ | w - ξ ∈ V} := fun ξ hξ => h1 (by
      simp only [mem_Iio] at hξ
      simp only [mem_Ioi]
      linarith)
    apply EventuallyLE.antisymm
    · exact ae_le_set.2 (by rw [sdiff_eq_empty.2 hsub1, measure_empty])
    · exact Iio_ae_eq_Iic.symm.le.trans
        (ae_le_set.2 (by rw [sdiff_eq_empty.2 hsub2, measure_empty]))
  rw [setIntegral_congr_set hS]

/-- Ray case of (I) for a lower set `L ⊆ (-∞,0)` and an upper set `V ⊆ [0,∞)`. -/
theorem ray_I_sets (hφi : Integrable φ) (hT : TP2 φ) {L V : Set ℝ} (hL : IsLowerSet L)
    (hV : IsUpperSet V) (hLm : MeasurableSet L) (hVm : MeasurableSet V) (hLneg : ∀ t ∈ L, t < 0)
    (hVpos : ∀ t ∈ V, 0 ≤ t) {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) :
    (conv (L.indicator 1) φ y - conv (L.indicator 1) φ z) *
        (conv (V.indicator 1) φ y - conv (V.indicator 1) φ x) ≤
      (conv (L.indicator 1) φ x - conv (L.indicator 1) φ y) *
        (conv (V.indicator 1) φ z - conv (V.indicator 1) φ y) := by
  rcases L.eq_empty_or_nonempty with hL0 | hLne
  · subst hL0; simp [conv]
  rcases V.eq_empty_or_nonempty with hV0 | hVne
  · subst hV0; simp [conv]
  have hLb : BddAbove L := ⟨0, fun t ht => (hLneg t ht).le⟩
  have hVb : BddBelow V := ⟨0, fun t ht => hVpos t ht⟩
  set a := sSup L with ha
  set b := sInf V with hb
  have ha0 : a ≤ 0 := csSup_le hLne fun t ht => (hLneg t ht).le
  have hb0 : 0 ≤ b := le_csInf hVne hVpos
  have hL1 : Iio a ⊆ L := fun t ht => by
    obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup hLne ht
    exact hL hts.le hs
  have hL2 : L ⊆ Iic a := fun t ht => le_csSup hLb ht
  have hV1 : Ioi b ⊆ V := fun t ht => by
    obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt hVne ht
    exact hV hst.le hs
  have hV2 : V ⊆ Ici b := fun t ht => csInf_le hVb ht
  have hIic : ∀ c : ℝ, IntegrableOn φ (Iic c) := fun c => hφi.integrableOn
  have dL : ∀ p q : ℝ, conv (L.indicator 1) φ p - conv (L.indicator 1) φ q =
      ∫ u in (p - a)..(q - a), φ u := fun p q => by
    rw [conv_ind_lower hφi hL1 hL2 hLm, conv_ind_lower hφi hL1 hL2 hLm,
      ← intervalIntegral.integral_Iic_sub_Iic (hIic _) (hIic _)]
    ring
  have dV : ∀ p q : ℝ, conv (V.indicator 1) φ q - conv (V.indicator 1) φ p =
      ∫ u in (p - b)..(q - b), φ u := fun p q => by
    rw [conv_ind_upper hV1 hV2 hVm, conv_ind_upper hV1 hV2 hVm,
      intervalIntegral.integral_Iic_sub_Iic (hIic _) (hIic _)]
  rw [dL, dL, dV, dV]
  exact ray_I hφi hT hxy hyz (by linarith)

/-- (I) for a fixed lower set `L` and a general monotone `B ≥ 0` vanishing on `(-∞,0)`. -/
theorem ineq_I_L (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ) (hT : TP2 φ) {L : Set ℝ}
    (hL : IsLowerSet L) (hLm : MeasurableSet L) (hLneg : ∀ t ∈ L, t < 0) {B : ℝ → ℝ}
    (hB : Monotone B) (hB0 : ∀ t, 0 ≤ B t) (hBz : ∀ t, t < 0 → B t = 0)
    (hBi : ∀ w, Integrable (fun ξ => B (w - ξ) * φ ξ)) {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) :
    (conv (L.indicator 1) φ y - conv (L.indicator 1) φ z) * (conv B φ y - conv B φ x) ≤
      (conv (L.indicator 1) φ x - conv (L.indicator 1) φ y) * (conv B φ z - conv B φ y) := by
  set β := conv (L.indicator 1) φ y - conv (L.indicator 1) φ z
  set α := conv (L.indicator 1) φ x - conv (L.indicator 1) φ y
  have := lc3_nonpos hφ0 hφi hB0 hB.measurable hBi x y z (-β) (β + α) (-α) ?_
  · linarith
  · intro l hl
    have hV : IsUpperSet {t | l < B t} := fun s t hst hs => lt_of_lt_of_le hs (hB hst)
    have hVm : MeasurableSet {t | l < B t} := measurableSet_lt measurable_const hB.measurable
    have hVpos : ∀ t ∈ {t | l < B t}, 0 ≤ t := by
      intro t ht
      by_contra h
      push Not at h
      rw [mem_ofPred_eq, hBz t h] at ht
      linarith
    have := ray_I_sets hφi hT hL hV hLm hVm hLneg hVpos hxy hyz
    linarith

/-- **Inequality (I)**: `β γ ≤ α δ` for the antitone left part `A` and monotone right part `B`. -/
theorem ineq_I (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ) (hT : TP2 φ) {A B : ℝ → ℝ}
    (hA : Antitone A) (hB : Monotone B) (hA0 : ∀ t, 0 ≤ A t) (hB0 : ∀ t, 0 ≤ B t)
    (hAz : ∀ t, 0 ≤ t → A t = 0) (hBz : ∀ t, t < 0 → B t = 0)
    (hAi : ∀ w, Integrable (fun ξ => A (w - ξ) * φ ξ))
    (hBi : ∀ w, Integrable (fun ξ => B (w - ξ) * φ ξ)) {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) :
    (conv A φ y - conv A φ z) * (conv B φ y - conv B φ x) ≤
      (conv A φ x - conv A φ y) * (conv B φ z - conv B φ y) := by
  set γ := conv B φ y - conv B φ x
  set δ := conv B φ z - conv B φ y
  have := lc3_nonpos hφ0 hφi hA0 hA.measurable hAi x y z (-δ) (γ + δ) (-γ) ?_
  · linarith
  · intro l hl
    have hL : IsLowerSet {t | l < A t} := fun s t hts hs => lt_of_lt_of_le hs (hA hts)
    have hLm : MeasurableSet {t | l < A t} := measurableSet_lt measurable_const hA.measurable
    have hLneg : ∀ t ∈ {t | l < A t}, t < 0 := by
      intro t ht
      by_contra h
      push Not at h
      rw [mem_ofPred_eq, hAz t h] at ht
      linarith
    have := ineq_I_L hφ0 hφi hT hL hLm hLneg hB hB0 hBz hBi hxy hyz
    linarith

/-- **Inequality (II)**: `β b₁ ≤ α (K - b₂)` for the antitone left part `A` and the
`[0,K]`-valued remainder `e` vanishing on `(-∞,0)`. -/
theorem ineq_II (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ) (hφ1 : ∫ t, φ t = 1) (hT : TP2 φ)
    {A e : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hA : Antitone A) (hA0 : ∀ t, 0 ≤ A t)
    (hAz : ∀ t, 0 ≤ t → A t = 0) (hAi : ∀ w, Integrable (fun ξ => A (w - ξ) * φ ξ))
    (he0 : ∀ t, 0 ≤ e t) (heK : ∀ t, e t ≤ K) (hez : ∀ t, t < 0 → e t = 0) (hem : Measurable e)
    {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) :
    (conv A φ y - conv A φ z) * (conv e φ y - conv e φ x) ≤
      (conv A φ x - conv A φ y) * (K - (conv e φ y - conv e φ z)) := by
  set b1 := conv e φ y - conv e φ x
  set b2 := conv e φ y - conv e φ z
  have := lc3_nonpos hφ0 hφi hA0 hA.measurable hAi x y z (-(K - b2)) (b1 + (K - b2)) (-b1) ?_
  · linarith
  · intro l hl
    have hL : IsLowerSet {t | l < A t} := fun s t hts hs => lt_of_lt_of_le hs (hA hts)
    have hLm : MeasurableSet {t | l < A t} := measurableSet_lt measurable_const hA.measurable
    have heL : ∀ t ∈ {t | l < A t}, e t = 0 := by
      intro t ht
      apply hez
      by_contra h
      push Not at h
      rw [mem_ofPred_eq, hAz t h] at ht
      linarith
    have := ray_II hφ0 hφi hφ1 hT hL hLm hK he0 heK heL hem hxy hyz
    linarith

/-- The decomposition `g = c + A + B + e` of a function of class `C_0(K)`:
`A ≥ 0` antitone and supported in `(-∞,0)`, `B ≥ 0` monotone and supported in `[0,∞)`,
`e ∈ [0,K]` supported in `[0,∞)`. (`B = M - c` with `M t = inf_{v ≥ t} g v`.) -/
theorem decomp {g : ℝ → ℝ} {K : ℝ} (hgm : Measurable g) (hgA : AntitoneOn g (Iio 0))
    (hgK : NonKDecreasingOn g K (Ici 0)) (hgb : BddBelow (g '' Iio 0)) :
    ∃ (c : ℝ) (A B e : ℝ → ℝ), (∀ t, g t = c + A t + B t + e t) ∧ Antitone A ∧ Monotone B ∧
      (∀ t, 0 ≤ A t) ∧ (∀ t, 0 ≤ B t) ∧ (∀ t, 0 ≤ e t) ∧ (∀ t, e t ≤ K) ∧
      (∀ t, 0 ≤ t → A t = 0) ∧ (∀ t, t < 0 → B t = 0) ∧ (∀ t, t < 0 → e t = 0) ∧
      Measurable e ∧ (∀ t, A t ≤ g t - c) ∧ (∀ t, B t ≤ g t - c) := by
  have hK0 : 0 ≤ K := by
    have := hgK 0 (mem_Ici.2 le_rfl) 0 (mem_Ici.2 le_rfl) le_rfl
    linarith
  obtain ⟨c1, hc1⟩ := hgb
  set c := min c1 (g 0 - K) with hc
  have hgc : ∀ t, c ≤ g t := by
    intro t
    rcases lt_or_ge t 0 with ht | ht
    · exact (min_le_left _ _).trans (hc1 ⟨t, ht, rfl⟩)
    · have := hgK 0 (mem_Ici.2 le_rfl) t (mem_Ici.2 ht) ht
      exact (min_le_right _ _).trans (by linarith)
  have hbdd : ∀ t : ℝ, BddBelow (range fun v : Ici t => g v) := fun t =>
    ⟨c, by rintro _ ⟨v, rfl⟩; exact hgc v⟩
  set M : ℝ → ℝ := fun t => ⨅ v : Ici t, g v with hM
  have hMle : ∀ t, M t ≤ g t := fun t => ciInf_le (hbdd t) ⟨t, mem_Ici.2 le_rfl⟩
  have hMge : ∀ t, c ≤ M t := fun t => le_ciInf fun v => hgc v
  have hMK : ∀ t, 0 ≤ t → g t - K ≤ M t := fun t ht => le_ciInf fun v => by
    have := hgK t (mem_Ici.2 ht) v (mem_Ici.2 (le_trans ht v.2)) v.2
    linarith
  have hMmono : Monotone M := fun s t hst =>
    le_ciInf fun v => ciInf_le (hbdd s) ⟨v, mem_Ici.2 (le_trans hst v.2)⟩
  refine ⟨c, fun t => if t < 0 then g t - c else 0, fun t => if t < 0 then 0 else M t - c,
    fun t => if t < 0 then 0 else g t - M t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    by_cases ht : t < 0
    · simp only [if_pos ht]; ring
    · simp only [if_neg ht]; ring
  · intro s t hst
    by_cases ht : t < 0
    · have hs : s < 0 := lt_of_le_of_lt hst ht
      simp only [if_pos ht, if_pos hs]
      linarith [hgA (mem_Iio.2 hs) (mem_Iio.2 ht) hst]
    · simp only [if_neg ht]
      by_cases hs : s < 0
      · simp only [if_pos hs]; linarith [hgc s]
      · simp only [if_neg hs]; exact le_rfl
  · intro s t hst
    by_cases hs : s < 0
    · simp only [if_pos hs]
      by_cases ht : t < 0
      · simp only [if_pos ht]; exact le_rfl
      · simp only [if_neg ht]; linarith [hMge t]
    · have ht : ¬ t < 0 := fun ht => hs (lt_of_le_of_lt hst ht)
      simp only [if_neg hs, if_neg ht]
      linarith [hMmono hst]
  · intro t
    by_cases ht : t < 0
    · simp only [if_pos ht]; linarith [hgc t]
    · simp only [if_neg ht]; exact le_rfl
  · intro t
    by_cases ht : t < 0
    · simp only [if_pos ht]; exact le_rfl
    · simp only [if_neg ht]; linarith [hMge t]
  · intro t
    by_cases ht : t < 0
    · simp only [if_pos ht]; exact le_rfl
    · simp only [if_neg ht]; linarith [hMle t]
  · intro t
    by_cases ht : t < 0
    · simp only [if_pos ht]; exact hK0
    · simp only [if_neg ht]; linarith [hMK t (not_lt.1 ht)]
  · intro t ht
    simp only [if_neg (not_lt.2 ht)]
  · intro t ht
    simp only [if_pos ht]
  · intro t ht
    simp only [if_pos ht]
  · exact Measurable.ite measurableSet_Iio measurable_const (hgm.sub hMmono.measurable)
  · intro t
    by_cases ht : t < 0
    · simp only [if_pos ht]; exact le_rfl
    · simp only [if_neg ht]; linarith [hgc t]
  · intro t
    by_cases ht : t < 0
    · simp only [if_pos ht]; linarith [hgc t]
    · simp only [if_neg ht]; linarith [hMle t]

/-- **CORE LEMMA (S2).** Convolution with a TP2 probability density `φ` maps the class `C_0(K)`
(antitone on `(-∞,0)`, non-`K`-decreasing on `[0,∞)`) into quasi-`K`-convex functions:
for `x < y < z`, `F y ≤ max (F x) (F z + K)` where `F = conv g φ`. -/
theorem conv_quasiK {φ g : ℝ → ℝ} {K : ℝ} (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ)
    (hφ1 : ∫ t, φ t = 1) (hT : TP2 φ) (hgm : Measurable g) (hgA : AntitoneOn g (Iio 0))
    (hgK : NonKDecreasingOn g K (Ici 0)) (hgb : BddBelow (g '' Iio 0))
    (hgi : ∀ w, Integrable (fun ξ => g (w - ξ) * φ ξ)) {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    conv g φ y ≤ max (conv g φ x) (conv g φ z + K) := by
  have hK : 0 ≤ K := by
    have := hgK 0 (mem_Ici.2 le_rfl) 0 (mem_Ici.2 le_rfl) le_rfl
    linarith
  obtain ⟨c, A, B, e, hdec, hA, hB, hA0, hB0, he0, heK, hAz, hBz, hez, hem, hAg, hBg⟩ :=
    decomp hgm hgA hgK hgb
  have hgc : ∀ w, Integrable (fun ξ => (g (w - ξ) - c) * φ ξ) := fun w => by
    have := (hgi w).sub (hφi.const_mul c)
    refine this.congr (ae_of_all _ fun ξ => ?_)
    simp only [Pi.sub_apply]
    ring
  have dom : ∀ h : ℝ → ℝ, Measurable h → (∀ t, 0 ≤ h t) → (∀ t, h t ≤ g t - c) →
      ∀ w, Integrable (fun ξ => h (w - ξ) * φ ξ) := by
    intro h hm h0 hle w
    refine (hgc w).mono ((hm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
      hφi.aestronglyMeasurable) (ae_of_all _ fun ξ => ?_)
    have hle' := hle (w - ξ)
    have h0' := h0 (w - ξ)
    rw [norm_mul, norm_mul, Real.norm_of_nonneg h0',
      Real.norm_of_nonneg (show 0 ≤ g (w - ξ) - c by linarith)]
    exact mul_le_mul_of_nonneg_right hle' (norm_nonneg _)
  have hAi := dom A hA.measurable hA0 hAg
  have hBi := dom B hB.measurable hB0 hBg
  have hei : ∀ w, Integrable (fun ξ => e (w - ξ) * φ ξ) := fun w =>
    hφi.bdd_mul (c := K) (hem.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (ae_of_all _ fun ξ => by rw [Real.norm_eq_abs, abs_of_nonneg (he0 _)]; exact heK _)
  have hF : ∀ w, conv g φ w = c + conv A φ w + conv B φ w + conv e φ w := by
    intro w
    unfold conv
    have : (fun ξ => g (w - ξ) * φ ξ) = fun ξ =>
        c * φ ξ + A (w - ξ) * φ ξ + B (w - ξ) * φ ξ + e (w - ξ) * φ ξ := by
      funext ξ; rw [hdec (w - ξ)]; ring
    have i1 : Integrable (fun ξ => c * φ ξ + A (w - ξ) * φ ξ) := (hφi.const_mul c).add (hAi w)
    have i2 : Integrable (fun ξ => c * φ ξ + A (w - ξ) * φ ξ + B (w - ξ) * φ ξ) :=
      i1.add (hBi w)
    rw [this, integral_add i2 (hei w), integral_add i1 (hBi w),
      integral_add (hφi.const_mul c) (hAi w), integral_const_mul, hφ1, mul_one]
  have hI := ineq_I hφ0 hφi hT hA hB hA0 hB0 hAz hBz hAi hBi hxy.le hyz.le
  have hII := ineq_II hφ0 hφi hφ1 hT hK hA hA0 hAz hAi he0 heK hez hem hxy.le hyz.le
  have hα : conv A φ y ≤ conv A φ x :=
    integral_mono (hAi y) (hAi x) fun ξ =>
      mul_le_mul_of_nonneg_right (hA (by linarith : x - ξ ≤ y - ξ)) (hφ0 ξ)
  have hδ : conv B φ y ≤ conv B φ z :=
    integral_mono (hBi y) (hBi z) fun ξ =>
      mul_le_mul_of_nonneg_right (hB (by linarith : y - ξ ≤ z - ξ)) (hφ0 ξ)
  have hEy : conv e φ y ≤ K := by
    have := integral_mono (hei y) (hφi.const_mul K) fun ξ =>
      mul_le_mul_of_nonneg_right (heK (y - ξ)) (hφ0 ξ)
    rw [integral_const_mul, hφ1, mul_one] at this
    exact this
  have hEz := conv_nonneg hφ0 he0 z
  have hFx := hF x
  have hFy := hF y
  have hFz := hF z
  by_contra hcon
  push Not at hcon
  rw [max_lt_iff] at hcon
  obtain ⟨h1, h2⟩ := hcon
  set α := conv A φ x - conv A φ y with hαd
  set β := conv A φ y - conv A φ z with hβd
  set γ := conv B φ y - conv B φ x with hγd
  set δ := conv B φ z - conv B φ y with hδd
  set b1 := conv e φ y - conv e φ x with hb1d
  set b2 := conv e φ y - conv e φ z with hb2d
  have k1 : 0 < γ + b1 - α := by linarith
  have k2 : δ + K - b2 < β := by linarith
  have hβpos : 0 < β := by linarith
  nlinarith [mul_pos hβpos k1, mul_nonneg (sub_nonneg.2 hα) (sub_nonneg.2 k2.le)]

/-- The same, in the Definitions' `QuasiKConvexOn` form. -/
theorem conv_quasiKConvexOn {φ g : ℝ → ℝ} {K : ℝ} (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ)
    (hφ1 : ∫ t, φ t = 1) (hT : TP2 φ) (hgm : Measurable g) (hgA : AntitoneOn g (Iio 0))
    (hgK : NonKDecreasingOn g K (Ici 0)) (hgb : BddBelow (g '' Iio 0))
    (hgi : ∀ w, Integrable (fun ξ => g (w - ξ) * φ ξ)) :
    QuasiKConvexOn (conv g φ) K univ := by
  have hK : 0 ≤ K := by
    have := hgK 0 (mem_Ici.2 le_rfl) 0 (mem_Ici.2 le_rfl) le_rfl
    linarith
  refine ⟨convex_univ, fun x _ y _ hxy l hl0 hl1 => ?_⟩
  have h1 : x ≤ l * x + (1 - l) * y := by nlinarith [mul_nonneg (sub_nonneg.2 hl1) (sub_nonneg.2 hxy)]
  have h2 : l * x + (1 - l) * y ≤ y := by nlinarith [mul_nonneg hl0 (sub_nonneg.2 hxy)]
  rcases h1.lt_or_eq with h1 | h1
  · rcases h2.lt_or_eq with h2 | h2
    · exact conv_quasiK hφ0 hφi hφ1 hT hgm hgA hgK hgb hgi h1 h2
    · rw [h2]; exact le_max_of_le_right (by linarith)
  · rw [← h1]; exact le_max_left _ _

/-- `IsPF n` with `1 ≤ n` forces `φ ≥ 0` (the `k = 1` determinant). -/
theorem nonneg_of_isPF {n : ℕ} (hn : 1 ≤ n) (h : IsPF n φ) (t : ℝ) : 0 ≤ φ t := by
  have := h.2 1 le_rfl hn ![t] ![0] (Subsingleton.strictMono _) (Subsingleton.strictMono _)
  simpa [Matrix.det_fin_one] using this

/-- `IsPF n` with `2 ≤ n` gives the pointwise `TP2` inequality (the `k = 2` determinant). -/
theorem tp2_of_isPF {n : ℕ} (hn : 2 ≤ n) (h : IsPF n φ) : TP2 φ := by
  intro x1 x2 t1 t2 hx ht
  have hxm : StrictMono ![x1, x2] := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    simpa using hx
  have htm : StrictMono ![t1, t2] := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    simpa using ht
  have := h.2 2 (by norm_num) hn ![x1, x2] ![t1, t2] hxm htm
  rw [Matrix.det_fin_two] at this
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  linarith

/-- The four facts about a Pólya density that the core lemma uses. -/
theorem polya_facts (h : IsPolyaDensity φ) :
    (∀ t, 0 ≤ φ t) ∧ Integrable φ ∧ ∫ t, φ t = 1 ∧ TP2 φ := by
  have h2 := h.1 2 (by norm_num)
  exact ⟨nonneg_of_isPF (by norm_num) h2, h2.1.1, h.2, tp2_of_isPF le_rfl h2⟩

end Core

end Lib
end PorteusSS

/-! ## S3: regularity, first moment, invariant `PInv`, and `QKHyp` for `h_n` -/

open MeasureTheory Filter Topology Set


namespace PorteusSS
namespace Lib
section S3

theorem shift_ae_subseq {φ : ℝ → ℝ} (hφ : Integrable φ) {yn : ℕ → ℝ} {y : ℝ}
    (hy : Tendsto yn atTop (𝓝 y)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ t : ℝ, Tendsto (fun j => φ (yn (ns j) - t)) atTop (𝓝 (φ (y - t))) := by
  let g : Lp ℝ 1 (volume : Measure ℝ) := hφ.toL1 φ
  have hmp : ∀ w : ℝ, MeasurePreserving (fun t : ℝ => w - t) volume volume :=
    fun w => Measure.measurePreserving_sub_left volume w
  let gm : ℝ → C(ℝ, ℝ) := fun w => ⟨fun t => w - t, by fun_prop⟩
  have hgm : Continuous gm := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    simp only [gm]
    exact continuous_fst.sub continuous_snd
  have hcont : Continuous fun w : ℝ => Lp.compMeasurePreserving (gm w) (hmp w) g :=
    (continuous_const (y := g)).compMeasurePreservingLp hgm hmp (by norm_num)
  have hT := (hcont.tendsto y).comp hy
  have hm := tendstoInMeasure_of_tendsto_Lp hT
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  have hg : (g : ℝ → ℝ) =ᵐ[volume] φ := hφ.coeFn_toL1
  have hw : ∀ w : ℝ, (Lp.compMeasurePreserving (gm w) (hmp w) g : ℝ → ℝ) =ᵐ[volume]
      fun t => φ (w - t) := fun w => by
    have h1 := Lp.coeFn_compMeasurePreserving g (hmp w)
    have h2 := (hmp w).quasiMeasurePreserving.ae_eq_comp hg
    exact h1.trans h2
  have hall : ∀ᵐ t : ℝ, ∀ n : ℕ, (Lp.compMeasurePreserving (gm (yn n)) (hmp (yn n)) g : ℝ → ℝ) t
      = φ (yn n - t) := ae_all_iff.2 fun n => hw (yn n)
  filter_upwards [hae, hall, hw y] with t h1 h2 h3
  rw [h3] at h1
  exact h1.congr fun i => h2 (ns i)


theorem measurable_of_piecewiseContinuous {f : ℝ → ℝ} (h : PiecewiseContinuousOn f univ) :
    Measurable f := by
  obtain ⟨A, -, hcont, -⟩ := h
  have hAm : MeasurableSet (↑A : Set ℝ) := A.measurableSet
  refine measurable_of_restrict_of_restrict_compl hAm ?_ ?_
  · exact measurable_of_countable _
  · have h2 : ContinuousOn f (↑A : Set ℝ)ᶜ := by
      rw [compl_eq_univ_sdiff]; exact hcont
    exact (continuousOn_iff_continuous_domRestrict.1 h2).measurable

theorem lsc_comp_cont {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {F : β → ℝ}
    (hF : LowerSemicontinuous F) {g : α → β} (hg : Continuous g) :
    LowerSemicontinuous (fun x => F (g x)) := by
  intro x b hb
  exact (hg.tendsto x).eventually (hF (g x) b hb)

theorem integrable_t_iff (u ψ : ℝ → ℝ) (y : ℝ) :
    Integrable (fun ξ => u (y - ξ) * ψ ξ) ↔ Integrable (fun t => u t * ψ (y - t)) := by
  constructor
  · intro h
    have := h.comp_sub_left y
    simpa [sub_sub_cancel] using this
  · intro h
    have := h.comp_sub_left y
    simpa [sub_sub_cancel] using this

theorem int_shift_one {φ : ℝ → ℝ} (hφ1 : ∫ t, φ t = 1) (z : ℝ) : ∫ t, φ (z - t) = 1 := by
  have := integral_sub_left_eq_self φ (volume : Measure ℝ) z
  rw [this, hφ1]

theorem nkd_cInf {c : ℝ → ℝ} {c0 K0 cInf KInf : ℝ} (hc : IsOrderingCost c c0 K0 cInf KInf)
    {f : ℝ → ℝ}
    (hnkd : ∀ k ∈ slopeSet c, NonKDecreasingOn (fun x => k * x + f x) (Kc c k) univ)
    {x y : ℝ} (hxy : x ≤ y) : cInf * x + f x ≤ cInf * y + f y + KInf := by
  by_contra hcon
  push Not at hcon
  set U : Set (ℝ × ℝ) := {p | p.1 * y + f y + p.2 < p.1 * x + f x} with hU
  have hUo : U ∈ 𝓝 ((cInf, KInf) : ℝ × ℝ) := by
    have hopen : IsOpen U := isOpen_lt (by fun_prop) (by fun_prop)
    exact hopen.mem_nhds hcon
  obtain ⟨z, hz, hzpos⟩ := ((hc.lim_top U hUo).and (eventually_gt_atTop 0)).exists
  obtain ⟨k, K, hkK⟩ := C2_nonempty hc hzpos
  have hkU : (k, K) ∈ U := hz hkK
  have hK0 : 0 ≤ K := C1_K_nonneg hc.zero hkK.1
  have hk : k ∈ slopeSet c := ⟨K, hK0, z, hzpos, hkK⟩
  have hKc : Kc c k = K := Kc_eq_of_C2 hzpos hkK
  have := hnkd k hk x (mem_univ _) y (mem_univ _) hxy
  simp only [hKc] at this
  simp only [hU, mem_ofPred_eq] at hkU
  linarith

/-- `cInf t + f t` is bounded below on all of `ℝ`. -/
theorem p_lower {c : ℝ → ℝ} {c0 K0 cInf KInf : ℝ} (hc : IsOrderingCost c c0 K0 cInf KInf)
    {f : ℝ → ℝ}
    (hnkd : ∀ k ∈ slopeSet c, NonKDecreasingOn (fun x => k * x + f x) (Kc c k) univ)
    (hanti : AntitoneOn (fun x => cInf * x + f x) (Iio 0)) (t : ℝ) :
    cInf * (-1) + f (-1) - |KInf| ≤ cInf * t + f t := by
  rcases le_total t (-1) with ht | ht
  · have := hanti (show t ∈ Iio (0:ℝ) by simp only [mem_Iio]; linarith)
      (show (-1:ℝ) ∈ Iio (0:ℝ) by simp) ht
    simp only at this
    have := abs_nonneg KInf
    linarith
  · have := nkd_cInf hc hnkd ht
    have := le_abs_self KInf
    linarith

/-! Moment of a one-sided Polya density -/

theorem moment_integrable {φ : ℝ → ℝ} (hd : IsOneSidedPolyaDensity φ) :
    Integrable (fun ξ => ξ * φ ξ) := by
  obtain ⟨h0, hi, h1, hT⟩ := polya_facts hd.1
  have hneg := hd.2
  obtain ⟨p, hp⟩ : ∃ p, 0 < φ p := by
    by_contra hcon
    push Not at hcon
    have : ∀ t, φ t = 0 := fun t => le_antisymm (hcon t) (h0 t)
    simp [this] at h1
  have hp0 : 0 ≤ p := by
    by_contra h
    push Not at h
    have := hneg p h
    linarith
  set g : ℝ → ENNReal := fun t => ENNReal.ofReal (φ t) with hg
  have hgm : AEMeasurable g volume := hi.1.aemeasurable.ennreal_ofReal
  have hg1 : ∫⁻ t, g t = 1 := by
    have := ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ h0)
    rw [h1] at this
    simpa using this.symm
  -- pointwise ratio bound
  have hratio : ∀ v, p < v → ENNReal.ofReal (φ p) * ∫⁻ t, (Ioi v).indicator g t ≤ g v := by
    intro v hv
    set d := v - p with hd
    have hdpos : 0 < d := by linarith
    have e1 : ∫⁻ t, (Ioi v).indicator g t = ∫⁻ s, (Ioi p).indicator (fun s => g (s + d)) s := by
      rw [← lintegral_add_right_eq_self ((Ioi v).indicator g) d]
      apply lintegral_congr
      intro s
      by_cases hs : p < s
      · have : v < s + d := by linarith
        simp [indicator, hs, this]
      · have : ¬ v < s + d := by simp only [not_lt]; linarith [not_lt.1 hs]
        simp [indicator, hs, this]
    rw [e1, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ∫⁻ s, ENNReal.ofReal (φ p) * (Ioi p).indicator (fun s => g (s + d)) s
        ≤ ∫⁻ s, g v * (Ioi p).indicator g s := by
          apply lintegral_mono
          intro s
          by_cases hs : p < s
          · simp only [indicator, mem_Ioi, hs, if_true]
            have hT' := hT (p + d) (s + d) 0 d (by linarith) hdpos
            have e2 : p + d - d = p := by ring
            have e3 : s + d - 0 = s + d := by ring
            have e4 : p + d - 0 = v := by rw [hd]; ring
            have e5 : s + d - d = s := by ring
            rw [e2, e3, e4, e5] at hT'
            simp only [hg]
            rw [← ENNReal.ofReal_mul (h0 _), ← ENNReal.ofReal_mul (h0 _)]
            exact ENNReal.ofReal_le_ofReal hT'
          · simp [indicator, hs]
      _ = g v * ∫⁻ s, (Ioi p).indicator g s := by
          rw [lintegral_const_mul' _ _ ?_]
          simp only [hg]; exact ENNReal.ofReal_ne_top
      _ ≤ g v * 1 := by
          gcongr
          rw [← hg1]
          exact lintegral_mono fun s => indicator_le_self _ _ s
      _ = g v := mul_one _
  -- Tonelli
  set X : ENNReal := ∫⁻ t, ENNReal.ofReal (t - p) * g t with hX
  have hXswap : X = ∫⁻ v, ∫⁻ t, (Ioo p t).indicator (fun _ => g t) v := by
    rw [hX]
    have : ∀ t, ENNReal.ofReal (t - p) * g t = ∫⁻ v, (Ioo p t).indicator (fun _ => g t) v := by
      intro t
      rw [lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo, mul_comm]
    simp_rw [this]
    apply lintegral_lintegral_swap
    -- AEMeasurable of uncurry
    have h1 : AEMeasurable (fun q : ℝ × ℝ => g q.1) (volume.prod volume) :=
      hgm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have h2 : MeasurableSet {q : ℝ × ℝ | q.2 ∈ Ioo p q.1} := by
      have : {q : ℝ × ℝ | q.2 ∈ Ioo p q.1} = {q | p < q.2} ∩ {q | q.2 < q.1} := by
        ext q; simp [mem_Ioo]
      rw [this]
      exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_fst)
    have h3 := h1.indicator h2
    refine h3.congr (Eventually.of_forall fun q => ?_)
    simp [indicator, Function.uncurry, mem_Ioo]
  have hinner : ∀ v, ∫⁻ t, (Ioo p t).indicator (fun _ => g t) v
      = if p < v then ∫⁻ t, (Ioi v).indicator g t else 0 := by
    intro v
    by_cases hv : p < v
    · rw [if_pos hv]
      apply lintegral_congr
      intro t
      by_cases ht : v < t
      · simp [indicator, hv, ht]
      · simp [indicator, ht]
    · rw [if_neg hv]
      simp [indicator, hv]
  have hbound : ENNReal.ofReal (φ p) * X ≤ 1 := by
    rw [hXswap, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ∫⁻ v, ENNReal.ofReal (φ p) * ∫⁻ t, (Ioo p t).indicator (fun _ => g t) v
        ≤ ∫⁻ v, g v := by
          apply lintegral_mono
          intro v
          dsimp only
          rw [hinner v]
          by_cases hv : p < v
          · rw [if_pos hv]; exact hratio v hv
          · rw [if_neg hv]; simp
      _ = 1 := hg1
  have hXfin : X ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (by simpa using hp)] at hbound
    simp at hbound
  -- integrability of the positive part
  have hpos : Integrable (fun ξ => max (ξ - p) 0 * φ ξ) := by
    refine ⟨((continuous_id.sub continuous_const).max continuous_const).aestronglyMeasurable.mul
      hi.1, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ξ => mul_nonneg (le_max_right _ _) (h0 ξ))]
    have : ∀ ξ, ENNReal.ofReal (max (ξ - p) 0 * φ ξ) = ENNReal.ofReal (ξ - p) * g ξ := by
      intro ξ
      rw [ENNReal.ofReal_mul (le_max_right _ _)]
      simp [hg, ENNReal.ofReal_max]
    simp_rw [this]
    exact lt_top_iff_ne_top.2 hXfin
  refine Integrable.mono' ((hi.const_mul p).add hpos)
    (continuous_id.aestronglyMeasurable.mul hi.1) (ae_of_all _ fun ξ => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  by_cases hξ : ξ < 0
  · simp [hneg ξ hξ]
  · push Not at hξ
    rw [abs_of_nonneg (mul_nonneg hξ (h0 ξ))]
    rcases le_total ξ p with h | h
    · rw [max_eq_right (by linarith)]
      nlinarith [h0 ξ]
    · rw [max_eq_left (by linarith)]
      nlinarith [h0 ξ]

/-! Affine convolution identity and lower bound -/

theorem conv_affine {φ u : ℝ → ℝ} (hφi : Integrable φ) (hφ1 : ∫ t, φ t = 1)
    (hmom : Integrable (fun ξ => ξ * φ ξ)) (a y : ℝ)
    (hu : Integrable (fun ξ => u (y - ξ) * φ ξ)) :
    Integrable (fun ξ => (a * (y - ξ) + u (y - ξ)) * φ ξ) ∧
    conv (fun t => a * t + u t) φ y = a * (y - ∫ ξ, ξ * φ ξ) + conv u φ y := by
  have h1 : Integrable (fun ξ => a * (y - ξ) * φ ξ) := by
    have := (hφi.const_mul (a * y)).sub (hmom.const_mul a)
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    simp only [Pi.sub_apply]; ring
  have e1 : ∫ ξ, a * (y - ξ) * φ ξ = a * (y - ∫ ξ, ξ * φ ξ) := by
    have : ∀ ξ, a * (y - ξ) * φ ξ = a * y * φ ξ - a * (ξ * φ ξ) := fun ξ => by ring
    simp_rw [this]
    rw [integral_sub (hφi.const_mul _) (hmom.const_mul _), integral_const_mul, integral_const_mul,
      hφ1]
    ring
  have this : ∀ ξ, (a * (y - ξ) + u (y - ξ)) * φ ξ = a * (y - ξ) * φ ξ + u (y - ξ) * φ ξ :=
    fun ξ => by ring
  refine ⟨(h1.add hu).congr (Eventually.of_forall fun ξ => (this ξ).symm), ?_⟩
  unfold conv
  simp only [this]
  rw [integral_add h1 hu, e1]

theorem conv_lower {φ u : ℝ → ℝ} (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ)
    (hφ1 : ∫ t, φ t = 1) {Q : ℝ} (hu : ∀ t, -Q ≤ u t) (y : ℝ)
    (hint : Integrable (fun ξ => u (y - ξ) * φ ξ)) : -Q ≤ conv u φ y := by
  have h1 : ∫ ξ, -Q * φ ξ ≤ ∫ ξ, u (y - ξ) * φ ξ :=
    integral_mono (hφi.const_mul _) hint (fun ξ => mul_le_mul_of_nonneg_right (hu _) (hφ0 ξ))
  rw [integral_const_mul, hφ1] at h1
  simpa [conv] using h1


/-! Lower semicontinuity of translates -/

theorem lsc_nonneg {φ u : ℝ → ℝ} (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ) (hu0 : ∀ t, 0 ≤ u t)
    (hint : ∀ y, Integrable (fun t => u t * φ (y - t))) :
    LowerSemicontinuous (fun y => ∫ t, u t * φ (y - t)) := by
  intro y b hb
  have hb' : b < ∫ t, u t * φ (y - t) := hb
  by_contra hcon
  have hfr : ∃ᶠ z in 𝓝 y, ∫ t, u t * φ (z - t) ≤ b := by
    by_contra hnot
    apply hcon
    rw [Filter.not_frequently] at hnot
    exact hnot.mono fun z hz => not_le.1 hz
  obtain ⟨zs, hzs, hfs⟩ := Filter.frequently_iff_seq_frequently.1 hfr
  obtain ⟨ψ, hψ, hψP⟩ := Filter.extraction_of_frequently_atTop hfs
  have hz2 : Tendsto (fun n => zs (ψ n)) atTop (𝓝 y) := hzs.comp hψ.tendsto_atTop
  obtain ⟨ns, hns, hae⟩ := shift_ae_subseq hφi hz2
  set w : ℕ → ℝ := fun j => zs (ψ (ns j)) with hw
  have hbw : ∀ j, ∫ t, u t * φ (w j - t) ≤ b := fun j => hψP (ns j)
  have hb0 : 0 ≤ b :=
    le_trans (integral_nonneg fun t => mul_nonneg (hu0 t) (hφ0 _)) (hbw 0)
  set F : ℕ → ℝ → ENNReal :=
    fun j t => ENNReal.ofReal (u t) * ENNReal.ofReal (φ (w j - t)) with hF
  have hFint : ∀ j, ∫⁻ t, F j t = ENNReal.ofReal (∫ t, u t * φ (w j - t)) := by
    intro j
    rw [ofReal_integral_eq_lintegral_ofReal (hint (w j))
      (ae_of_all _ fun t => mul_nonneg (hu0 t) (hφ0 _))]
    apply lintegral_congr
    intro t
    simp only [hF]
    rw [ENNReal.ofReal_mul (hu0 t)]
  have hFm : ∀ j, AEMeasurable (F j) volume := by
    intro j
    have := (hint (w j)).1.aemeasurable.ennreal_ofReal
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [hF]
    rw [ENNReal.ofReal_mul (hu0 t)]
  set L : ℝ → ENNReal := fun t => ENNReal.ofReal (u t) * ENNReal.ofReal (φ (y - t)) with hL
  have hLint : ∫⁻ t, L t = ENNReal.ofReal (∫ t, u t * φ (y - t)) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hint y)
      (ae_of_all _ fun t => mul_nonneg (hu0 t) (hφ0 _))]
    apply lintegral_congr
    intro t
    simp only [hL]
    rw [ENNReal.ofReal_mul (hu0 t)]
  have hlim : ∀ᵐ t, liminf (fun j => F j t) atTop = L t := by
    filter_upwards [hae] with t ht
    apply Filter.Tendsto.liminf_eq
    exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal ht) (Or.inr ENNReal.ofReal_ne_top)
  have hfatou := lintegral_liminf_le' (μ := volume) (u := atTop) hFm
  have h1 : ∫⁻ t, L t ≤ ENNReal.ofReal b := by
    calc ∫⁻ t, L t = ∫⁻ t, liminf (fun j => F j t) atTop :=
          lintegral_congr_ae (hlim.mono fun t ht => ht.symm)
      _ ≤ liminf (fun j => ∫⁻ t, F j t) atTop := hfatou
      _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal b) atTop :=
          liminf_le_liminf (Eventually.of_forall fun j => by
            rw [hFint j]; exact ENNReal.ofReal_le_ofReal (hbw j))
      _ = ENNReal.ofReal b := liminf_const _
  rw [hLint] at h1
  have := (ENNReal.ofReal_le_ofReal_iff hb0).1 h1
  linarith

theorem lsc_shift {φ u : ℝ → ℝ} (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ) (hφ1 : ∫ t, φ t = 1)
    {Q : ℝ} (hu : ∀ t, -Q ≤ u t) (hint : ∀ y, Integrable (fun t => u t * φ (y - t))) :
    LowerSemicontinuous (fun y => ∫ t, u t * φ (y - t)) := by
  have hint' : ∀ y, Integrable (fun t => (u t + Q) * φ (y - t)) := fun y =>
    ((hint y).add ((hφi.comp_sub_left y).const_mul Q)).congr
      (Eventually.of_forall fun t => by simp only [Pi.add_apply]; ring)
  have h1 := lsc_nonneg hφ0 hφi (u := fun t => u t + Q) (fun t => by linarith [hu t]) hint'
  have hEq : ∀ z, ∫ t, (u t + Q) * φ (z - t) = (∫ t, u t * φ (z - t)) + Q := by
    intro z
    have : ∀ t, (u t + Q) * φ (z - t) = u t * φ (z - t) + Q * φ (z - t) := fun t => by ring
    simp_rw [this]
    rw [integral_add (hint z) ((hφi.comp_sub_left z).const_mul Q), integral_const_mul,
      int_shift_one hφ1 z]
    ring
  intro y b hb
  have hb' : b < ∫ t, u t * φ (y - t) := hb
  have := h1 y (b + Q) (by simp only [hEq y]; linarith)
  filter_upwards [this] with z hz
  simp only [hEq z] at hz
  show b < ∫ t, u t * φ (z - t)
  linarith

theorem lsc_const_mul {g : ℝ → ℝ} (hg : LowerSemicontinuous g) {α : ℝ} (hα : 0 ≤ α) :
    LowerSemicontinuous (fun y => α * g y) := by
  rcases hα.eq_or_lt with rfl | hpos
  · intro y b hb
    exact Eventually.of_forall fun z => by simpa using hb
  · intro y b hb
    have hb' : b / α < g y := by rw [div_lt_iff₀ hpos]; linarith
    filter_upwards [hg y (b / α) hb'] with z hz
    have hz' : b / α < g z := hz
    rw [div_lt_iff₀ hpos] at hz'
    show b < α * g z
    linarith

/-! Convolution limits -/

theorem conv_atTop {φ u : ℝ → ℝ} (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ)
    (hφ1 : ∫ t, φ t = 1) {Q : ℝ} (hQ : 0 ≤ Q) (hu : ∀ t, -Q ≤ u t)
    (hint : ∀ y, Integrable (fun ξ => u (y - ξ) * φ ξ)) (hlim : Tendsto u atTop atTop) :
    Tendsto (fun y => conv u φ y) atTop atTop := by
  rw [tendsto_atTop]
  intro B
  set B' := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  have hBB' : B ≤ B' := le_max_left _ _
  have hmass : ∀ᶠ n : ℕ in atTop, (1:ℝ)/2 < ∫ ξ in Iic (n:ℝ), φ ξ := by
    have := tendsto_setIntegral_of_monotone (μ := volume) (f := φ) (s := fun n : ℕ => Iic (n:ℝ))
      (fun n => measurableSet_Iic) (fun a b hab => Iic_subset_Iic.2 (by exact_mod_cast hab))
      hφi.integrableOn
    have hU : (⋃ n : ℕ, Iic (n:ℝ)) = univ := by
      ext x
      simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
      exact exists_nat_ge x
    rw [hU, setIntegral_univ, hφ1] at this
    exact this.eventually (lt_mem_nhds (by norm_num))
  obtain ⟨N, hN⟩ := hmass.exists
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hlim.eventually_ge_atTop (2 * (B' + Q)))
  refine eventually_atTop.2 ⟨T + N, fun y hy => ?_⟩
  set M1 := 2 * (B' + Q) with hM1
  have hpt : ∀ ξ, -Q * φ ξ + (M1 + Q) * (Iic (N:ℝ)).indicator φ ξ ≤ u (y - ξ) * φ ξ := by
    intro ξ
    by_cases hξ : ξ ≤ N
    · have := hT (y - ξ) (by linarith)
      have h2 : (Iic (N:ℝ)).indicator φ ξ = φ ξ := indicator_of_mem (mem_Iic.2 hξ) _
      rw [h2]
      nlinarith [hφ0 ξ]
    · have h2 : (Iic (N:ℝ)).indicator φ ξ = 0 := indicator_of_notMem (by simpa using hξ) _
      rw [h2]
      nlinarith [hφ0 ξ, hu (y - ξ)]
  have hI : Integrable (fun ξ => -Q * φ ξ + (M1 + Q) * (Iic (N:ℝ)).indicator φ ξ) :=
    (hφi.const_mul _).add ((hφi.indicator measurableSet_Iic).const_mul _)
  have h1 := integral_mono hI (hint y) hpt
  rw [integral_add (hφi.const_mul _) ((hφi.indicator measurableSet_Iic).const_mul _),
    integral_const_mul, integral_const_mul, hφ1, integral_indicator measurableSet_Iic] at h1
  have h2 : conv u φ y = ∫ ξ, u (y - ξ) * φ ξ := rfl
  rw [h2]
  nlinarith

theorem conv_atBot {φ u : ℝ → ℝ} (hφ0 : ∀ t, 0 ≤ φ t) (hφi : Integrable φ)
    (hφ1 : ∫ t, φ t = 1) (hneg : ∀ x, x < 0 → φ x = 0)
    (hint : ∀ y, Integrable (fun ξ => u (y - ξ) * φ ξ)) (hlim : Tendsto u atBot atTop) :
    Tendsto (fun y => conv u φ y) atBot atTop := by
  rw [tendsto_atTop]
  intro B
  obtain ⟨T, hT⟩ := eventually_atBot.1 (hlim.eventually_ge_atTop B)
  refine eventually_atBot.2 ⟨T, fun y hy => ?_⟩
  have hpt : ∀ ξ, B * φ ξ ≤ u (y - ξ) * φ ξ := by
    intro ξ
    by_cases hξ : ξ < 0
    · simp [hneg ξ hξ]
    · push Not at hξ
      exact mul_le_mul_of_nonneg_right (hT (y - ξ) (by linarith)) (hφ0 ξ)
  have h1 := integral_mono (hφi.const_mul B) (hint y) hpt
  rw [integral_const_mul, hφ1] at h1
  have h2 : conv u φ y = ∫ ξ, u (y - ξ) * φ ξ := rfl
  rw [h2]
  linarith


/-! The model layer -/

section Model
variable {c m φ f : ℝ → ℝ} {α c0 K0 cInf KInf : ℝ}

theorem m_integ (hM : IsModel c m φ α c0 K0 cInf KInf) (y : ℝ) :
    Integrable (fun ξ => m (y - ξ) * φ ξ) :=
  hM.m_pfIntegrable φ hM.density.1.1 y

theorem m_lower (hM : IsModel c m φ α c0 K0 cInf KInf) (hA1 : AssumptionA1 m α c0 cInf) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ b : ℝ, 0 ≤ b → b ≤ c0 - α * cInf → ∀ t, -Q ≤ b * t + m t := by
  obtain ⟨M0, hM0⟩ := hM.m_bddBelow
  have hm0 : ∀ t, M0 ≤ m t := fun t => hM0 ⟨t, rfl⟩
  set b0 := c0 - α * cInf with hb0
  set Q1 := -(b0 * (-1) + m (-1)) with hQ1
  set Q2 := b0 - M0 with hQ2
  refine ⟨max (max Q1 Q2) 0, le_max_right _ _, ?_⟩
  intro b hb0' hb1 t
  have e1 : Q1 ≤ max (max Q1 Q2) 0 := (le_max_left _ _).trans (le_max_left _ _)
  have e2 : Q2 ≤ max (max Q1 Q2) 0 := (le_max_right _ _).trans (le_max_left _ _)
  rcases le_total t (-1) with ht | ht
  · have h := hA1 (show t ∈ Iio (0:ℝ) by simp only [mem_Iio]; linarith)
      (show (-1:ℝ) ∈ Iio (0:ℝ) by simp) ht
    simp only at h
    have : (b0 - b) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    nlinarith
  · have := mul_nonneg hb0' (show 0 ≤ t + 1 by linarith)
    have := hm0 t
    nlinarith

theorem hStep_affine (hM : IsModel c m φ α c0 K0 cInf KInf)
    (hfint : ∀ y, Integrable (fun ξ => f (y - ξ) * φ ξ)) (a b y : ℝ)
    (hb : b = a + α * cInf) :
    b * y + hStep m φ α f y = conv (fun t => a * t + m t) φ y
      + α * conv (fun t => cInf * t + f t) φ y + b * ∫ ξ, ξ * φ ξ := by
  obtain ⟨h0, hi, h1, hT⟩ := polya_facts hM.density.1
  have mom := moment_integrable hM.density
  have e1 := (conv_affine hi h1 mom a y (m_integ hM y)).2
  have e2 := (conv_affine hi h1 mom cInf y (hfint y)).2
  subst hb
  unfold hStep
  rw [e1, e2]
  ring

theorem hStep_lower_line (hM : IsModel c m φ α c0 K0 cInf KInf)
    (hA1 : AssumptionA1 m α c0 cInf)
    (hnkd : ∀ k ∈ slopeSet c, NonKDecreasingOn (fun x => k * x + f x) (Kc c k) univ)
    (hanti : AntitoneOn (fun x => cInf * x + f x) (Iio 0))
    (hfint : ∀ y, Integrable (fun ξ => f (y - ξ) * φ ξ)) (a b : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a ≤ c0 - α * cInf) (hb : b = a + α * cInf) :
    ∃ M : ℝ, ∀ y, -M ≤ b * y + hStep m φ α f y := by
  obtain ⟨h0, hi, h1, hT⟩ := polya_facts hM.density.1
  have mom := moment_integrable hM.density
  have hc := hM.cost
  obtain ⟨Q, hQ0, hQ⟩ := m_lower hM hA1
  set P := -(cInf * (-1) + f (-1) - |KInf|) with hP
  refine ⟨Q + α * P - b * ∫ ξ, ξ * φ ξ, fun y => ?_⟩
  have hq := conv_lower h0 hi h1 (u := fun t => a * t + m t) (hQ a ha0 ha1) y
    (conv_affine hi h1 mom a y (m_integ hM y)).1
  have hp := conv_lower h0 hi h1 (Q := P) (u := fun t => cInf * t + f t)
    (fun t => by
      have := p_lower hc hnkd hanti t
      show -P ≤ cInf * t + f t
      rw [hP]; linarith) y (conv_affine hi h1 mom cInf y (hfint y)).1
  have := hStep_affine hM hfint a b y hb
  have h3 := mul_le_mul_of_nonneg_left hp hM.alpha_nonneg
  nlinarith

theorem hStep_lsc (hM : IsModel c m φ α c0 K0 cInf KInf)
    (hnkd : ∀ k ∈ slopeSet c, NonKDecreasingOn (fun x => k * x + f x) (Kc c k) univ)
    (hanti : AntitoneOn (fun x => cInf * x + f x) (Iio 0))
    (hfint : ∀ y, Integrable (fun ξ => f (y - ξ) * φ ξ)) :
    LowerSemicontinuous (hStep m φ α f) := by
  obtain ⟨h0, hi, h1, hT⟩ := polya_facts hM.density.1
  have mom := moment_integrable hM.density
  have hc := hM.cost
  obtain ⟨M0, hM0⟩ := hM.m_bddBelow
  have hmlsc : LowerSemicontinuous (fun y => conv m φ y) := by
    have : (fun y => conv m φ y) = fun y => ∫ t, m t * φ (y - t) :=
      funext fun y => conv_eq_t m φ y
    rw [this]
    exact lsc_shift h0 hi h1 (Q := -M0) (fun t => by have := hM0 ⟨t, rfl⟩; linarith)
      (fun y => (integrable_t_iff m φ y).1 (m_integ hM y))
  have hplsc : LowerSemicontinuous (fun y => conv (fun t => cInf * t + f t) φ y) := by
    have : (fun y => conv (fun t => cInf * t + f t) φ y)
        = fun y => ∫ t, (cInf * t + f t) * φ (y - t) :=
      funext fun y => conv_eq_t _ φ y
    rw [this]
    refine lsc_shift h0 hi h1 (Q := -(cInf * (-1) + f (-1) - |KInf|))
      (fun t => ?_) (fun y => (integrable_t_iff _ φ y).1
        (conv_affine hi h1 mom cInf y (hfint y)).1)
    have := p_lower hc hnkd hanti t
    show -(-(cInf * (-1) + f (-1) - |KInf|)) ≤ cInf * t + f t
    linarith
  have hfconv : (fun y => conv f φ y) = fun y => conv (fun t => cInf * t + f t) φ y
      + (-(cInf * (y - ∫ ξ, ξ * φ ξ))) := by
    funext y
    rw [(conv_affine hi h1 mom cInf y (hfint y)).2]
    ring
  have hflsc : LowerSemicontinuous (fun y => conv f φ y) := by
    rw [hfconv]
    exact hplsc.add (Continuous.lowerSemicontinuous (by fun_prop))
  exact hmlsc.add (lsc_const_mul hflsc hM.alpha_nonneg)

theorem hStep_atTop (hM : IsModel c m φ α c0 K0 cInf KInf)
    (hA1 : AssumptionA1 m α c0 cInf) (hA4 : AssumptionA4 m α cInf)
    (hnkd : ∀ k ∈ slopeSet c, NonKDecreasingOn (fun x => k * x + f x) (Kc c k) univ)
    (hanti : AntitoneOn (fun x => cInf * x + f x) (Iio 0))
    (hfint : ∀ y, Integrable (fun ξ => f (y - ξ) * φ ξ)) :
    Tendsto (fun y => cInf * y + hStep m φ α f y) atTop atTop := by
  obtain ⟨h0, hi, h1, hT⟩ := polya_facts hM.density.1
  have mom := moment_integrable hM.density
  have hc := hM.cost
  have hα0 := hM.alpha_nonneg
  have hα1 := hM.alpha_le_one
  have hcI := cInf_nonneg hc
  have hc0I := cInf_le_c0 hc
  obtain ⟨Q, hQ0, hQ⟩ := m_lower hM hA1
  set a := (1 - α) * cInf with ha
  have ha0 : 0 ≤ a := mul_nonneg (by linarith) hcI
  have ha1 : a ≤ c0 - α * cInf := by rw [ha]; nlinarith
  have hb : cInf = a + α * cInf := by rw [ha]; ring
  have hq : Tendsto (fun y => conv (fun t => a * t + m t) φ y) atTop atTop :=
    conv_atTop h0 hi h1 hQ0 (fun t => hQ a ha0 ha1 t)
      (fun y => (conv_affine hi h1 mom a y (m_integ hM y)).1) hA4
  set P := -(cInf * (-1) + f (-1) - |KInf|) with hP
  refine tendsto_atTop_mono (fun y => ?_)
    (tendsto_atTop_add_const_right _ (-(α * P) + cInf * ∫ ξ, ξ * φ ξ) hq)
  have hp := conv_lower h0 hi h1 (Q := P) (u := fun t => cInf * t + f t)
    (fun t => by
      have := p_lower hc hnkd hanti t
      show -P ≤ cInf * t + f t
      rw [hP]; linarith) y (conv_affine hi h1 mom cInf y (hfint y)).1
  have := hStep_affine hM hfint a cInf y hb
  have h3 := mul_le_mul_of_nonneg_left hp hα0
  show conv (fun t => a * t + m t) φ y + (-(α * P) + cInf * ∫ ξ, ξ * φ ξ)
    ≤ cInf * y + hStep m φ α f y
  nlinarith

theorem hStep_atBot (hM : IsModel c m φ α c0 K0 cInf KInf)
    (hA2 : AssumptionA2 m α c0 cInf)
    (hnkd : ∀ k ∈ slopeSet c, NonKDecreasingOn (fun x => k * x + f x) (Kc c k) univ)
    (hanti : AntitoneOn (fun x => cInf * x + f x) (Iio 0))
    (hfint : ∀ y, Integrable (fun ξ => f (y - ξ) * φ ξ)) :
    Tendsto (fun y => c0 * y + hStep m φ α f y) atBot atTop := by
  obtain ⟨h0, hi, h1, hT⟩ := polya_facts hM.density.1
  have mom := moment_integrable hM.density
  have hc := hM.cost
  have hα0 := hM.alpha_nonneg
  set a := c0 - α * cInf with ha
  have hb : c0 = a + α * cInf := by rw [ha]; ring
  have hq : Tendsto (fun y => conv (fun t => a * t + m t) φ y) atBot atTop :=
    conv_atBot h0 hi h1 hM.density.2
      (fun y => (conv_affine hi h1 mom a y (m_integ hM y)).1) hA2
  set P := -(cInf * (-1) + f (-1) - |KInf|) with hP
  refine tendsto_atTop_mono (fun y => ?_)
    (tendsto_atTop_add_const_right _ (-(α * P) + c0 * ∫ ξ, ξ * φ ξ) hq)
  have hp := conv_lower h0 hi h1 (Q := P) (u := fun t => cInf * t + f t)
    (fun t => by
      have := p_lower hc hnkd hanti t
      show -P ≤ cInf * t + f t
      rw [hP]; linarith) y (conv_affine hi h1 mom cInf y (hfint y)).1
  have := hStep_affine hM hfint a c0 y hb
  have h3 := mul_le_mul_of_nonneg_left hp hα0
  show conv (fun t => a * t + m t) φ y + (-(α * P) + c0 * ∫ ξ, ξ * φ ξ)
    ≤ c0 * y + hStep m φ α f y
  nlinarith

end Model


section Model2
variable {c m φ f : ℝ → ℝ} {α c0 K0 cInf KInf : ℝ}

/-- The invariant `I(n)` for a value function `f`. -/
structure PInv (c : ℝ → ℝ) (cInf : ℝ) (φ f : ℝ → ℝ) : Prop where
  integ : ∀ y, Integrable (fun ξ => f (y - ξ) * φ ξ)
  nkd : ∀ k ∈ slopeSet c, NonKDecreasingOn (fun x => k * x + f x) (Kc c k) univ
  anti : AntitoneOn (fun x => cInf * x + f x) (Iio 0)
  meas : Measurable f
  locbdd : ∀ R : ℝ, ∃ B : ℝ, ∀ x, |x| ≤ R → |f x| ≤ B

theorem locbdd_of_nkd (hc : IsOrderingCost c c0 K0 cInf KInf)
    (hnkd : ∀ k ∈ slopeSet c, NonKDecreasingOn (fun x => k * x + f x) (Kc c k) univ) (R : ℝ) :
    ∃ B : ℝ, ∀ x, |x| ≤ R → |f x| ≤ B := by
  obtain ⟨k, hk⟩ := one_mem_slopeSet hc
  have hk0 := slope_nonneg hc hk
  refine ⟨|f R| + |f (-R)| + 2 * k * |R| + |Kc c k|, fun x hx => ?_⟩
  have hxR := abs_le.1 hx
  have hR : |R| = R := abs_of_nonneg (by linarith)
  have h1 := hnkd k hk x (mem_univ _) R (mem_univ _) hxR.2
  have h2 := hnkd k hk (-R) (mem_univ _) x (mem_univ _) hxR.1
  simp only at h1 h2
  have e1 := le_abs_self (f R)
  have e2 := neg_abs_le (f R)
  have e3 := le_abs_self (f (-R))
  have e4 := neg_abs_le (f (-R))
  have e5 := le_abs_self (Kc c k)
  have e6 := neg_abs_le (Kc c k)
  have := abs_nonneg (f R)
  have := abs_nonneg (f (-R))
  rw [hR]
  have h3 : k * (R - x) ≤ 2 * k * R := by nlinarith
  have h4 : k * (x + R) ≤ 2 * k * R := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith

theorem PInv_zero {f0 : ℝ → ℝ} (hM : IsModel c m φ α c0 K0 cInf KInf)
    (hA5 : AssumptionA5 c f0 cInf) : PInv c cInf φ f0 :=
  { integ := fun y => hA5.2.1 φ hM.density.1.1 y
    nkd := hA5.2.2.2
    anti := hA5.2.2.1
    meas := measurable_of_piecewiseContinuous hA5.1
    locbdd := locbdd_of_nkd hM.cost hA5.2.2.2 }

/-- The value-function operator for an abstract one-period cost `h`. -/
noncomputable def Vh (c h : ℝ → ℝ) (x : ℝ) : ℝ := ⨅ y : Ici x, c ((y : ℝ) - x) + h y

theorem valueFn_succ_eq (c m φ f0 : ℝ → ℝ) (α : ℝ) (n : ℕ) :
    valueFn c m φ f0 α (n + 1) = Vh c (hStep m φ α (valueFn c m φ f0 α n)) := rfl

theorem hFn_succ_eq (c m φ f0 : ℝ → ℝ) (α : ℝ) (n : ℕ) :
    hFn c m φ f0 α (n + 1) = hStep m φ α (valueFn c m φ f0 α n) := rfl

theorem Vh_bdd (hc : IsOrderingCost c c0 K0 cInf KInf) {h : ℝ → ℝ} {M : ℝ}
    (hlow : ∀ y, -M ≤ cInf * y + h y) (x : ℝ) :
    BddBelow (range fun y : Ici x => c ((y : ℝ) - x) + h y) := by
  refine ⟨-M - cInf * x, ?_⟩
  rintro _ ⟨y, rfl⟩
  have := cInf_mul_le hc (sub_nonneg.2 y.2)
  have := hlow y
  simp only
  nlinarith

theorem Vh_le (hc : IsOrderingCost c c0 K0 cInf KInf) {h : ℝ → ℝ} {M : ℝ}
    (hlow : ∀ y, -M ≤ cInf * y + h y) {x y : ℝ} (hy : x ≤ y) :
    Vh c h x ≤ c (y - x) + h y :=
  ciInf_le (Vh_bdd hc hlow x) (⟨y, hy⟩ : Ici x)

theorem Vh_ge (hc : IsOrderingCost c c0 K0 cInf KInf) {h : ℝ → ℝ} {M : ℝ}
    (hlow : ∀ y, -M ≤ cInf * y + h y) (x : ℝ) : -M - cInf * x ≤ Vh c h x := by
  have : Nonempty (Ici x) := ⟨⟨x, self_mem_Ici⟩⟩
  refine le_ciInf fun y => ?_
  have := cInf_mul_le hc (sub_nonneg.2 y.2)
  have := hlow y
  nlinarith

theorem Vh_eq (hc : IsOrderingCost c c0 K0 cInf KInf) {h : ℝ → ℝ} {M : ℝ}
    (hlow : ∀ y, -M ≤ cInf * y + h y) {x S : ℝ} (hS : S ∈ YsetH c h x) :
    Vh c h x = c (S - x) + h S := by
  have : Nonempty (Ici x) := ⟨⟨x, self_mem_Ici⟩⟩
  refine le_antisymm (Vh_le hc hlow hS.1) (le_ciInf fun y => ?_)
  exact hS.2 y y.2

theorem Vh_lsc (hc : IsOrderingCost c c0 K0 cInf KInf) {h : ℝ → ℝ}
    (hlsc : LowerSemicontinuous h) (hcoer : Tendsto (fun y => cInf * y + h y) atTop atTop)
    {M : ℝ} (hlow : ∀ y, -M ≤ cInf * y + h y) : LowerSemicontinuous (Vh c h) := by
  intro x0 b hb
  have hb' : b < Vh c h x0 := hb
  by_contra hcon
  have hfr : ∃ᶠ x in 𝓝 x0, Vh c h x ≤ b := by
    by_contra hnot
    apply hcon
    rw [Filter.not_frequently] at hnot
    exact hnot.mono fun z hz => not_le.1 hz
  obtain ⟨xs, hxs, hfs⟩ := Filter.frequently_iff_seq_frequently.1 hfr
  obtain ⟨ψ, hψ, hψP⟩ := Filter.extraction_of_frequently_atTop hfs
  set x : ℕ → ℝ := fun n => xs (ψ n) with hxdef
  have hx : Tendsto x atTop (𝓝 x0) := hxs.comp hψ.tendsto_atTop
  have hxb : ∀ n, Vh c h (x n) ≤ b := hψP
  set y : ℕ → ℝ := fun n => sSup (YsetH c h (x n)) with hydef
  have hy : ∀ n, y n ∈ YsetH c h (x n) := fun n => (YsetH_props hc hlsc hcoer (x n)).2.2
  have hval : ∀ n, c (y n - x n) + h (y n) ≤ b := fun n => by
    rw [← Vh_eq hc hlow (hy n)]; exact hxb n
  have hxy : ∀ n, x n ≤ y n := fun n => (hy n).1
  obtain ⟨Xmax, hXmax⟩ := hx.bddAbove_range
  obtain ⟨Xmin, hXmin⟩ := hx.bddBelow_range
  have hcI := cInf_nonneg hc
  obtain ⟨R, hR⟩ := eventually_atTop.1 (hcoer.eventually_gt_atTop (b + cInf * Xmax))
  have hyb : ∀ n, y n ∈ Icc Xmin R := by
    intro n
    refine ⟨(hXmin ⟨n, rfl⟩).trans (hxy n), ?_⟩
    by_contra hRn
    push Not at hRn
    have h1 := hR (y n) hRn.le
    have h2 := cInf_mul_le hc (sub_nonneg.2 (hxy n))
    have h3 := hval n
    have h4 : cInf * x n ≤ cInf * Xmax := mul_le_mul_of_nonneg_left (hXmax ⟨n, rfl⟩) hcI
    nlinarith
  obtain ⟨ys, -, ns, hns, hlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc Xmin R) hyb
  have hxlim : Tendsto (fun k => x (ns k)) atTop (𝓝 x0) := hx.comp hns.tendsto_atTop
  have hys : x0 ≤ ys := le_of_tendsto_of_tendsto' hxlim hlim (fun k => hxy (ns k))
  have hJc : LowerSemicontinuous (fun p : ℝ × ℝ => c (max (p.2 - p.1) 0)) := by
    have := lsc_comp_cont (lsc_cost_from hc 0) (g := fun p : ℝ × ℝ => p.2 - p.1) (by fun_prop)
    simpa using this
  have hJh : LowerSemicontinuous (fun p : ℝ × ℝ => h p.2) := lsc_comp_cont hlsc continuous_snd
  have hJ := hJc.add hJh
  have hpt : b < c (max (ys - x0) 0) + h ys := by
    rw [max_eq_left (sub_nonneg.2 hys)]
    exact lt_of_lt_of_le hb' (Vh_le hc hlow hys)
  have hev := hJ (x0, ys) b hpt
  have hT : Tendsto (fun k => (x (ns k), (y ∘ ns) k)) atTop (𝓝 (x0, ys)) :=
    hxlim.prodMk_nhds hlim
  obtain ⟨k, hk⟩ := (hT.eventually hev).exists
  simp only [Function.comp] at hk
  rw [max_eq_left (sub_nonneg.2 (hxy (ns k)))] at hk
  have := hval (ns k)
  linarith

theorem Vh_growth (hc : IsOrderingCost c c0 K0 cInf KInf) {h : ℝ → ℝ} {M : ℝ}
    (hlow : ∀ y, -M ≤ cInf * y + h y) (y0 : ℝ) :
    ∃ A B : ℝ, 0 ≤ B ∧ ∀ x ≤ y0, |Vh c h x| ≤ A + B * |x| := by
  have hcI := cInf_nonneg hc
  have hc0 := c0_nonneg hc
  refine ⟨|c0 * y0 + K0 + h y0| + |M|, c0 + cInf, by linarith, fun x hx => ?_⟩
  have hup : Vh c h x ≤ c0 * y0 + K0 + h y0 - c0 * x := by
    have := Vh_le hc hlow hx
    have := le_c0_line hc (sub_nonneg.2 hx)
    nlinarith
  have hlo := Vh_ge hc hlow x
  have e1 := le_abs_self (c0 * y0 + K0 + h y0)
  have e2 := le_abs_self M
  have e3 : c0 * (-x) ≤ c0 * |x| := mul_le_mul_of_nonneg_left (neg_le_abs x) hc0
  have e4 : cInf * x ≤ cInf * |x| := mul_le_mul_of_nonneg_left (le_abs_self x) hcI
  have e5 := mul_nonneg hcI (abs_nonneg x)
  have e6 := mul_nonneg hc0 (abs_nonneg x)
  have e7 := abs_nonneg M
  have e8 := abs_nonneg (c0 * y0 + K0 + h y0)
  rw [abs_le]
  constructor <;> nlinarith

theorem integ_of_growth {g : ℝ → ℝ} (hd : IsOneSidedPolyaDensity φ) (hgm : Measurable g)
    (hgr : ∀ y, ∃ A B : ℝ, 0 ≤ B ∧ ∀ x ≤ y, |g x| ≤ A + B * |x|) (y : ℝ) :
    Integrable (fun ξ => g (y - ξ) * φ ξ) := by
  obtain ⟨h0, hi, h1, hT⟩ := polya_facts hd.1
  have mom := moment_integrable hd
  obtain ⟨A, B, hB, hAB⟩ := hgr y
  refine Integrable.mono' ((hi.const_mul (A + B * |y|)).add (mom.const_mul B))
    ((hgm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul hi.1)
    (ae_of_all _ fun ξ => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  by_cases hξ : ξ < 0
  · simp [hd.2 ξ hξ]
  · push Not at hξ
    have h1 := hAB (y - ξ) (by linarith)
    have h2 : |y - ξ| ≤ |y| + ξ := by
      calc |y - ξ| ≤ |y| + |ξ| := abs_sub y ξ
        _ = |y| + ξ := by rw [abs_of_nonneg hξ]
    rw [abs_mul, abs_of_nonneg (h0 ξ)]
    have h3 : |g (y - ξ)| ≤ A + B * |y| + B * ξ := by nlinarith
    nlinarith [h0 ξ]

theorem locbdd_of_growth {g : ℝ → ℝ}
    (hgr : ∀ y, ∃ A B : ℝ, 0 ≤ B ∧ ∀ x ≤ y, |g x| ≤ A + B * |x|) (R : ℝ) :
    ∃ Bd : ℝ, ∀ x, |x| ≤ R → |g x| ≤ Bd := by
  obtain ⟨A, B, hB, hAB⟩ := hgr R
  refine ⟨A + B * R, fun x hx => ?_⟩
  have := hAB x (le_trans (le_abs_self x) hx)
  nlinarith [mul_le_mul_of_nonneg_left hx hB]

theorem hStep_lower (hM : IsModel c m φ α c0 K0 cInf KInf)
    (hA1 : AssumptionA1 m α c0 cInf) (hf : PInv c cInf φ f) :
    ∃ M : ℝ, ∀ y, -M ≤ cInf * y + hStep m φ α f y := by
  have hc := hM.cost
  have hα0 := hM.alpha_nonneg
  have hα1 := hM.alpha_le_one
  have hcI := cInf_nonneg hc
  have hc0I := cInf_le_c0 hc
  refine hStep_lower_line hM hA1 hf.nkd hf.anti hf.integ ((1 - α) * cInf) cInf
    (mul_nonneg (by linarith) hcI) (by nlinarith) (by ring)

/-- Deliverable 3+4: the next value function `Vh c (hStep ..)` is measurable, has integrable
translates against `φ`, is locally bounded, and grows at most linearly on `Iic y`. -/
theorem next_props (hM : IsModel c m φ α c0 K0 cInf KInf)
    (hA1 : AssumptionA1 m α c0 cInf) (hA4 : AssumptionA4 m α cInf) (hf : PInv c cInf φ f) :
    Measurable (Vh c (hStep m φ α f)) ∧
    (∀ y0 : ℝ, ∃ A B : ℝ, 0 ≤ B ∧ ∀ x ≤ y0, |Vh c (hStep m φ α f) x| ≤ A + B * |x|) ∧
    (∀ y, Integrable (fun ξ => Vh c (hStep m φ α f) (y - ξ) * φ ξ)) ∧
    (∀ R : ℝ, ∃ B : ℝ, ∀ x, |x| ≤ R → |Vh c (hStep m φ α f) x| ≤ B) := by
  have hc := hM.cost
  obtain ⟨M, hM'⟩ := hStep_lower hM hA1 hf
  have hlsc := hStep_lsc hM hf.nkd hf.anti hf.integ
  have hcoer := hStep_atTop hM hA1 hA4 hf.nkd hf.anti hf.integ
  have hmeas : Measurable (Vh c (hStep m φ α f)) :=
    (Vh_lsc hc hlsc hcoer hM').measurable
  have hgr := fun y0 => Vh_growth hc hM' y0
  exact ⟨hmeas, hgr, integ_of_growth hM.density hmeas hgr, locbdd_of_growth hgr⟩

end Model2

/-! ## S3 (c): `QKHyp` for `h = hStep m φ α f` from the core lemma -/

section QK
variable {c m φ f : ℝ → ℝ} {α c0 K0 cInf KInf : ℝ}

/-- `g_k = k· + m + α f` is nonincreasing on `(-∞,0)` (A1, invariant (iii), `k ≤ c₀`). -/
theorem gk_antitone (hM : IsModel c m φ α c0 K0 cInf KInf) (hA1 : AssumptionA1 m α c0 cInf)
    (hf : PInv c cInf φ f) {k : ℝ} (hk : k ∈ slopeSet c) :
    AntitoneOn (fun t => k * t + m t + α * f t) (Iio 0) := by
  intro s hs t ht hst
  have h1 := hA1 hs ht hst
  have h2 := hf.anti hs ht hst
  have hk0 := slope_le_c0 hM.cost hk
  simp only at h1 h2 ⊢
  have h3 := mul_le_mul_of_nonneg_left h2 hM.alpha_nonneg
  have h4 := mul_le_mul_of_nonneg_left hst (sub_nonneg.2 hk0)
  nlinarith

/-- `g_k` is non-`K_k`-decreasing on `[0,∞)` (A3 and invariant (ii)). -/
theorem gk_nkd (hM : IsModel c m φ α c0 K0 cInf KInf) (hA3 : AssumptionA3 c m α)
    (hf : PInv c cInf φ f) {k : ℝ} (hk : k ∈ slopeSet c) :
    NonKDecreasingOn (fun t => k * t + m t + α * f t) (Kc c k) (Ici 0) := by
  intro s hs t ht hst
  have h1 := hA3 k hk s hs t ht hst
  have h2 := hf.nkd k hk s (mem_univ _) t (mem_univ _) hst
  simp only at h1 h2 ⊢
  have h3 := mul_le_mul_of_nonneg_left h2 hM.alpha_nonneg
  nlinarith

/-- `g_k` is bounded below on `(-∞,0)`. -/
theorem gk_bdd (hM : IsModel c m φ α c0 K0 cInf KInf) (hA1 : AssumptionA1 m α c0 cInf)
    (hf : PInv c cInf φ f) {k : ℝ} (hk : k ∈ slopeSet c) :
    BddBelow ((fun t => k * t + m t + α * f t) '' Iio 0) := by
  obtain ⟨M0, hM0⟩ := hM.m_bddBelow
  have hk0 := slope_nonneg hM.cost hk
  have hcI := cInf_nonneg hM.cost
  have hα0 := hM.alpha_nonneg
  refine ⟨min (k * (-1) + m (-1) + α * f (-1))
    (-k + M0 + α * (cInf * (-1) + f (-1) - |KInf|)), ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  rcases le_total t (-1) with h | h
  · exact (min_le_left _ _).trans
      (gk_antitone hM hA1 hf hk ht (show (-1:ℝ) ∈ Iio 0 by norm_num) h)
  · refine (min_le_right _ _).trans ?_
    have hm : M0 ≤ m t := hM0 ⟨t, rfl⟩
    have hp := p_lower hM.cost hf.nkd hf.anti t
    have ht0 : t < 0 := ht
    have h5 := mul_nonpos_of_nonneg_of_nonpos hcI ht0.le
    have h6 : α * (cInf * (-1) + f (-1) - |KInf|) ≤ α * f t :=
      mul_le_mul_of_nonneg_left (by linarith) hα0
    have h7 := mul_nonneg hk0 (show 0 ≤ t + 1 by linarith)
    simp only
    nlinarith

theorem gk_integ (hM : IsModel c m φ α c0 K0 cInf KInf) (hf : PInv c cInf φ f) (k w : ℝ) :
    Integrable (fun ξ => (k * (w - ξ) + m (w - ξ) + α * f (w - ξ)) * φ ξ) := by
  obtain ⟨h0, hi, h1, hT⟩ := polya_facts hM.density.1
  have mom := moment_integrable hM.density
  have := (((hi.const_mul (k * w)).sub (mom.const_mul k)).add (m_integ hM w)).add
    ((hf.integ w).const_mul α)
  refine this.congr (Eventually.of_forall fun ξ => ?_)
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- `G_k = k· + h` is `conv g_k φ` plus the constant `k ∫ ξ φ ξ`. -/
theorem gk_conv (hM : IsModel c m φ α c0 K0 cInf KInf) (hf : PInv c cInf φ f) (k y : ℝ) :
    k * y + hStep m φ α f y
      = conv (fun t => k * t + m t + α * f t) φ y + k * ∫ ξ, ξ * φ ξ := by
  obtain ⟨h0, hi, h1, hT⟩ := polya_facts hM.density.1
  have mom := moment_integrable hM.density
  have hc : conv (fun t => k * t + m t + α * f t) φ y
      = ∫ ξ, ((k * y) * φ ξ - k * (ξ * φ ξ) + (m (y - ξ) * φ ξ + α * (f (y - ξ) * φ ξ))) := by
    unfold conv
    congr 1
    funext ξ
    ring
  have hh : hStep m φ α f y = (∫ ξ, m (y - ξ) * φ ξ) + α * ∫ ξ, f (y - ξ) * φ ξ := rfl
  have i1 : Integrable (fun ξ => k * y * φ ξ - k * (ξ * φ ξ)) := (hi.const_mul _).sub (mom.const_mul _)
  have i2 : Integrable (fun ξ => m (y - ξ) * φ ξ + α * (f (y - ξ) * φ ξ)) :=
    (m_integ hM y).add ((hf.integ y).const_mul α)
  have i3 : Integrable (fun ξ => k * y * φ ξ) := hi.const_mul _
  have i4 : Integrable (fun ξ => k * (ξ * φ ξ)) := mom.const_mul _
  rw [hc, hh, integral_add i1 i2, integral_sub i3 i4,
    integral_add (m_integ hM y) ((hf.integ y).const_mul α),
    integral_const_mul, integral_const_mul, integral_const_mul, h1]
  ring

/-- **S3 (c).** The quasi-`K_k`-convexity hypothesis of the structural lemma holds for
`h = hStep m φ α f` whenever `f` satisfies the invariant `PInv`. -/
theorem qkhyp_hStep (hM : IsModel c m φ α c0 K0 cInf KInf) (hA1 : AssumptionA1 m α c0 cInf)
    (hA3 : AssumptionA3 c m α) (hmm : Measurable m) (hf : PInv c cInf φ f) :
    QKHyp c (hStep m φ α f) := by
  obtain ⟨h0, hi, h1, hT⟩ := polya_facts hM.density.1
  intro k hk x y z hxy hyz hbad
  have hfm := hf.meas
  have hgm : Measurable (fun t => k * t + m t + α * f t) := by fun_prop
  have hq := conv_quasiK h0 hi h1 hT hgm (gk_antitone hM hA1 hf hk) (gk_nkd hM hA3 hf hk)
    (gk_bdd hM hA1 hf hk) (gk_integ hM hf k) hxy hyz
  have ex := gk_conv hM hf k x
  have ey := gk_conv hM hf k y
  have ez := gk_conv hM hf k z
  obtain ⟨hb1, hb2⟩ := hbad
  rcases le_max_iff.1 hq with h | h <;> linarith

/-- **Conclusion of the leaf for period `n`, given the invariant for `f_{n-1}`.** Everything
except the induction `PInv f_{n-1} → PInv f_n` (stage S4). -/
theorem leaf_of_PInv {f0 : ℝ → ℝ} (hM : IsModel c m φ α c0 K0 cInf KInf)
    (hm_pc : PiecewiseContinuousOn m univ) (hA1 : AssumptionA1 m α c0 cInf)
    (hA2 : AssumptionA2 m α c0 cInf) (hA3 : AssumptionA3 c m α) (hA4 : AssumptionA4 m α cInf)
    (n : ℕ) (hf : PInv c cInf φ (valueFn c m φ f0 α (n - 1))) :
    (∀ y : ℝ, Integrable (fun ξ => valueFn c m φ f0 α (n - 1) (y - ξ) * φ ξ)) ∧
      ∃ s S : ℝ, ∃ pol : ℝ → ℝ, IsGenSS pol s S ∧ ∀ x : ℝ, pol x ∈ Yset c m φ f0 α n x :=
  ⟨hf.integ, genSS_model c m φ f0 α c0 K0 cInf KInf n hM.cost
    (hStep_lsc hM hf.nkd hf.anti hf.integ) (hStep_atTop hM hA1 hA4 hf.nkd hf.anti hf.integ)
    (qkhyp_hStep hM hA1 hA3 (measurable_of_piecewiseContinuous hm_pc) hf)
    (hStep_atBot hM hA2 hf.nkd hf.anti hf.integ)⟩

end QK

end S3
end Lib
end PorteusSS

/-! ## S4: the invariant induction and the final theorem -/

open MeasureTheory Filter Topology Set

namespace PorteusSS
namespace Lib
section S4

variable {c m φ f : ℝ → ℝ} {α c0 K0 cInf KInf : ℝ}

/-- Increments of `c` on `[0,∞)` are at least `c_∞` times the step. -/
theorem c_incr_ge (hc : IsOrderingCost c c0 K0 cInf KInf) {z d : ℝ} (hz : 0 ≤ z) (hd : 0 ≤ d) :
    cInf * d ≤ c (z + d) - c z := by
  rcases hd.eq_or_lt with rfl | hd
  · simp
  set Z : ℝ := z + d + 1 with hZ
  obtain ⟨k, K, hkK⟩ := C2_nonempty hc (show 0 < Z by linarith)
  have hk : k ∈ slopeSet c := ⟨K, C1_K_nonneg hc.zero hkK.1, Z, by linarith, hkK⟩
  have hcI := cInf_le_slope hc hk
  have e1 : k * Z + K = c Z := hkK.1.1
  have e2 : c (z + d) ≤ k * (z + d) + K := hkK.1.2 (z + d) (by linarith)
  have hsl := hc.concave.slope_anti_adjacent (x := z) (y := z + d) (z := Z) (mem_Ici.2 hz)
    (mem_Ici.2 (by linarith)) (by linarith) (by linarith)
  have hZd : Z - (z + d) = 1 := by ring
  have hzd : z + d - z = d := by ring
  rw [hZd, div_one, hzd, le_div_iff₀ hd] at hsl
  have e3 : k * 1 ≤ c Z - c (z + d) := by nlinarith
  nlinarith

/-- `g = c_∞· + m + α f` is nonincreasing on `(-∞,0)`. -/
theorem gInf_antitone (hM : IsModel c m φ α c0 K0 cInf KInf) (hA1 : AssumptionA1 m α c0 cInf)
    (hf : PInv c cInf φ f) :
    AntitoneOn (fun t => cInf * t + m t + α * f t) (Iio 0) := by
  intro s hs t ht hst
  have h1 := hA1 hs ht hst
  have h2 := hf.anti hs ht hst
  have hk0 := cInf_le_c0 hM.cost
  simp only at h1 h2 ⊢
  have h3 := mul_le_mul_of_nonneg_left h2 hM.alpha_nonneg
  have h4 := mul_le_mul_of_nonneg_left hst (sub_nonneg.2 hk0)
  nlinarith

/-- `G_∞ = c_∞· + h` is nonincreasing on `(-∞,0)` (φ vanishes on `(-∞,0)`). -/
theorem GInf_antitone (hM : IsModel c m φ α c0 K0 cInf KInf) (hA1 : AssumptionA1 m α c0 cInf)
    (hf : PInv c cInf φ f) :
    AntitoneOn (fun y => cInf * y + hStep m φ α f y) (Iio 0) := by
  obtain ⟨h0, hi, h1, hT⟩ := polya_facts hM.density.1
  intro a ha b hb hab
  have ea := gk_conv hM hf cInf a
  have eb := gk_conv hM hf cInf b
  simp only
  rw [ea, eb]
  have hmono : conv (fun t => cInf * t + m t + α * f t) φ b
      ≤ conv (fun t => cInf * t + m t + α * f t) φ a := by
    unfold conv
    refine integral_mono (gk_integ hM hf cInf b) (gk_integ hM hf cInf a) (fun ξ => ?_)
    simp only
    by_cases hξ : ξ < 0
    · rw [hM.density.2 ξ hξ]; simp
    · push Not at hξ
      have ha' : a - ξ ∈ Iio (0:ℝ) := by
        have : a < 0 := ha
        show a - ξ < 0
        linarith
      have hb' : b - ξ ∈ Iio (0:ℝ) := by
        have : b < 0 := hb
        show b - ξ < 0
        linarith
      have := gInf_antitone hM hA1 hf ha' hb' (by linarith)
      exact mul_le_mul_of_nonneg_right this (h0 ξ)
  linarith

/-- **The invariant step** `I(n) → I(n+1)`. -/
theorem PInv_succ (hM : IsModel c m φ α c0 K0 cInf KInf) (hA1 : AssumptionA1 m α c0 cInf)
    (hA4 : AssumptionA4 m α cInf) (hf : PInv c cInf φ f) :
    PInv c cInf φ (Vh c (hStep m φ α f)) := by
  have hc := hM.cost
  obtain ⟨hmeas, -, hint, hloc⟩ := next_props hM hA1 hA4 hf
  obtain ⟨M, hlow⟩ := hStep_lower hM hA1 hf
  have hlsc := hStep_lsc hM hf.nkd hf.anti hf.integ
  have hcoer := hStep_atTop hM hA1 hA4 hf.nkd hf.anti hf.integ
  have hGa := GInf_antitone hM hA1 hf
  set h := hStep m φ α f with hh
  have hS : ∀ x, sSup (YsetH c h x) ∈ YsetH c h x := fun x => (YsetH_props hc hlsc hcoer x).2.2
  refine ⟨hint, ?_, ?_, hmeas, hloc⟩
  · intro k hk x _ y _ hxy
    have hSy := hS y
    have e1 := Vh_eq hc hlow hSy
    have e2 := Vh_le hc hlow (hxy.trans hSy.1)
    have e3 := subadd hc (sub_nonneg.2 hSy.1) (sub_nonneg.2 hxy)
    have e4 := le_supporting hk (sub_nonneg.2 hxy)
    rw [show sSup (YsetH c h y) - y + (y - x) = sSup (YsetH c h y) - x by ring] at e3
    have e5 := mul_sub k y x
    simp only
    linarith
  · intro x hx y hy hxy
    have hx0 : x < 0 := hx
    have hy0 : y < 0 := hy
    have hSx := hS x
    have e1 := Vh_eq hc hlow hSx
    simp only
    rcases le_or_gt y (sSup (YsetH c h x)) with hyS | hyS
    · have e2 := Vh_le hc hlow hyS
      have e3 := c_incr_ge hc (sub_nonneg.2 hyS) (sub_nonneg.2 hxy)
      rw [show sSup (YsetH c h x) - y + (y - x) = sSup (YsetH c h x) - x by ring] at e3
      have e5 := mul_sub cInf y x
      linarith
    · have e2 := Vh_le hc hlow (le_refl y)
      rw [sub_self, hc.zero, zero_add] at e2
      have hSx0 : sSup (YsetH c h x) ∈ Iio (0:ℝ) := show _ < (0:ℝ) by linarith
      have e3 := hGa hSx0 hy hyS.le
      have e4 := cInf_mul_le hc (sub_nonneg.2 hSx.1)
      have e5 := mul_sub cInf (sSup (YsetH c h x)) x
      simp only at e3
      linarith

/-- The invariant holds for every value function `f_n`. -/
theorem PInv_all {f0 : ℝ → ℝ} (hM : IsModel c m φ α c0 K0 cInf KInf)
    (hA1 : AssumptionA1 m α c0 cInf) (hA4 : AssumptionA4 m α cInf)
    (hA5 : AssumptionA5 c f0 cInf) (n : ℕ) : PInv c cInf φ (valueFn c m φ f0 α n) := by
  induction n with
  | zero => exact PInv_zero hM hA5
  | succ n ih =>
    rw [valueFn_succ_eq]
    exact PInv_succ hM hA1 hA4 ih

end S4
end Lib
end PorteusSS

open MeasureTheory Filter Topology Set PorteusSS in
theorem solution (c m φ f0 : ℝ → ℝ) (α c0 K0 cInf KInf : ℝ)
    (hmodel : IsModel c m φ α c0 K0 cInf KInf) (hm_pc : PiecewiseContinuousOn m univ)
    (hA1 : AssumptionA1 m α c0 cInf) (hA2 : AssumptionA2 m α c0 cInf)
    (hA3 : AssumptionA3 c m α) (hA4 : AssumptionA4 m α cInf)
    (hA5 : AssumptionA5 c f0 cInf) :
    ∀ n : ℕ, 1 ≤ n →
      (∀ y : ℝ, Integrable (fun ξ => valueFn c m φ f0 α (n - 1) (y - ξ) * φ ξ)) ∧
      ∃ s S : ℝ, ∃ pol : ℝ → ℝ, IsGenSS pol s S ∧ ∀ x : ℝ, pol x ∈ Yset c m φ f0 α n x := by
  intro n _
  exact Lib.leaf_of_PInv hmodel hm_pc hA1 hA2 hA3 hA4 n
    (Lib.PInv_all hmodel hA1 hA4 hA5 (n - 1))

