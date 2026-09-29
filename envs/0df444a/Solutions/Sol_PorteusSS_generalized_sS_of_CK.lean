-- Prove2me | solution 1 for PorteusSS.generalized_sS_of_CK
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:20:41.647811+00:00
-- url     : https://prove2.me/submissions/ada39aa2-e582-4dfd-adbd-4c14504da6e4

import Mathlib
import Definitions.Def_PorteusSS_Functions
import Definitions.Def_PorteusSS_OrderingCost
import Definitions.Def_PorteusSS_Model

open MeasureTheory Filter Topology Set

namespace PorteusSS

/-- Four-point inequality for a concave function on `[0, ∞)`. -/
lemma aux_gss_four {c : ℝ → ℝ} (hc : ConcaveOn ℝ (Ici 0) c) {p q r : ℝ} (hp : 0 ≤ p)
    (hpq : p ≤ q) (hqr : q ≤ r) : c p + c r ≤ c q + c (p + r - q) := by
  rcases eq_or_lt_of_le (hpq.trans hqr) with h | h
  · have hq : q = p := le_antisymm (h ▸ hqr) hpq
    have hr : r = p := h.symm
    rw [hq, hr, show p + p - p = p by ring]
  · have hrp : 0 < r - p := sub_pos.mpr h
    have hpm : p ∈ Ici (0:ℝ) := hp
    have hrm : r ∈ Ici (0:ℝ) := by simp only [mem_Ici]; linarith
    set a := (r - q) / (r - p) with ha_def
    set b := (q - p) / (r - p) with hb_def
    have ha : 0 ≤ a := div_nonneg (by linarith) hrp.le
    have hb : 0 ≤ b := div_nonneg (by linarith) hrp.le
    have hab : a + b = 1 := by
      rw [ha_def, hb_def]; field_simp; ring
    have h1 := hc.2 hpm hrm ha hb hab
    have h2 := hc.2 hpm hrm hb ha (by linarith [hab])
    simp only [smul_eq_mul] at h1 h2
    have e1 : a * p + b * r = q := by
      rw [ha_def, hb_def]; field_simp; ring
    have e2 : b * p + a * r = p + r - q := by
      rw [ha_def, hb_def]; field_simp; ring
    rw [e1] at h1
    rw [e2] at h2
    have key : a * c p + b * c r + (b * c p + a * c r) = c p + c r := by
      have hb' : b = 1 - a := by linarith
      rw [hb']; ring
    linarith

/-- Existence of a supporting line of minimal intercept at every `z > 0`. -/
lemma aux_gss_supp {c : ℝ → ℝ} (hc : ConcaveOn ℝ (Ici 0) c) (hc0 : c 0 = 0) {z : ℝ}
    (hz : 0 < z) : ∃ κ K : ℝ, 0 ≤ K ∧ (κ, K) ∈ C2 c z := by
  set T : Set ℝ := (fun t => (c z - c t) / (z - t)) '' Ico 0 z with hT
  have hTne : T.Nonempty := ⟨_, 0, ⟨le_refl 0, hz⟩, rfl⟩
  have hslope : ∀ t u, 0 ≤ t → t < z → z < u →
      (c u - c z) / (u - z) ≤ (c z - c t) / (z - t) := by
    intro t u ht htz hzu
    exact hc.slope_anti_adjacent (x := t) (y := z) (z := u) ht
      (by simp only [mem_Ici]; linarith) htz hzu
  have hTbdd : BddBelow T := by
    refine ⟨(c (z + 1) - c z) / ((z + 1) - z), ?_⟩
    rintro _ ⟨t, ⟨ht0, htz⟩, rfl⟩
    exact hslope t (z + 1) ht0 htz (by linarith)
  set κ := sInf T with hκ
  have hC1 : (κ, c z - κ * z) ∈ C1 c z := by
    refine ⟨by simp, fun y hy => ?_⟩
    show c y ≤ κ * y + (c z - κ * z)
    rcases lt_trichotomy y z with hyz | rfl | hyz
    · have : κ ≤ (c z - c y) / (z - y) := csInf_le hTbdd ⟨y, ⟨hy, hyz⟩, rfl⟩
      rw [le_div_iff₀ (by linarith)] at this
      linarith
    · linarith
    · have : (c y - c z) / (y - z) ≤ κ := by
        apply le_csInf hTne
        rintro _ ⟨t, ⟨ht0, htz⟩, rfl⟩
        exact hslope t y ht0 htz hyz
      rw [div_le_iff₀ (by linarith)] at this
      linarith
  have hK : 0 ≤ c z - κ * z := by
    have := hC1.2 0 le_rfl
    simp only [hc0, mul_zero, zero_add] at this
    linarith
  refine ⟨κ, c z - κ * z, hK, hC1, fun q hq => ?_⟩
  show c z - κ * z ≤ q.2
  have hq1 : q.1 ≤ κ := by
    apply le_csInf hTne
    rintro _ ⟨t, ⟨ht0, htz⟩, rfl⟩
    rw [le_div_iff₀ (by linarith)]
    have := hq.2 t ht0
    have := hq.1
    linarith
  have := mul_le_mul_of_nonneg_right hq1 hz.le
  have := hq.1
  linarith

/-- The set of optimal post-order levels for a generic `h`. -/
def aux_gss_Y (c h : ℝ → ℝ) (x : ℝ) : Set ℝ :=
  {S | x ≤ S ∧ ∀ y : ℝ, x ≤ y → c (S - x) + h S ≤ c (y - x) + h y}

lemma aux_gss_main (c h : ℝ → ℝ) (hcc : ConcaveOn ℝ (Ici 0) c) (hc0 : c 0 = 0)
    (hG : ∀ κ ∈ slopeSet c, CK (Kc c κ) (fun y => κ * y + h y))
    (hY : ∀ x : ℝ, (aux_gss_Y c h x).Nonempty) :
    ∃ s S : ℝ, ∃ pol : ℝ → ℝ, IsGenSS pol s S ∧ ∀ x : ℝ, pol x ∈ aux_gss_Y c h x := by
  obtain ⟨κ₀, K₀, hK₀, hC₀⟩ := aux_gss_supp hcc hc0 one_pos
  have hκ₀ : κ₀ ∈ slopeSet c := ⟨K₀, hK₀, 1, one_pos, hC₀⟩
  obtain ⟨-, hGcont, -, -, -, -, -, -, -, -, hGtend⟩ := hG κ₀ hκ₀
  have hcont : Continuous h := by
    have : Continuous (fun y => (κ₀ * y + h y) - κ₀ * y) :=
      hGcont.sub (continuous_const.mul continuous_id)
    simpa using this
  have hccont : ContinuousOn c (Ioi 0) := by
    have := hcc.continuousOn_interior
    rwa [interior_Ici] at this
  have hsub : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → c (a + b) ≤ c a + c b := by
    intro a b ha hb
    have := aux_gss_four hcc (p := 0) (q := a) (r := a + b) le_rfl ha (by linarith)
    rw [hc0, show (0:ℝ) + (a + b) - a = b by ring] at this
    linarith
  have hsupp : ∀ z : ℝ, 0 < z → ∃ κ K : ℝ, κ ∈ slopeSet c ∧ Kc c κ ≤ K ∧
      κ * z + K = c z ∧ ∀ y : ℝ, 0 ≤ y → c y ≤ κ * y + K := by
    intro z hz
    obtain ⟨κ, K, hK, hC⟩ := aux_gss_supp hcc hc0 hz
    refine ⟨κ, K, ⟨K, hK, z, hz, hC⟩, ?_, hC.1.1, hC.1.2⟩
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro K' ⟨z', hz', hC'⟩
      have := hC'.1.2 0 le_rfl
      simp only [hc0, mul_zero, zero_add] at this
      exact this
    · exact ⟨z, hz, hC⟩
  set N : Set ℝ := {x | ∀ y : ℝ, x ≤ y → h x ≤ c (y - x) + h y} with hN
  have hYN : ∀ x y : ℝ, y ∈ aux_gss_Y c h x → y ∈ N := by
    intro x y hy y' hyy'
    obtain ⟨hxy, hopt⟩ := hy
    by_contra hlt
    push Not at hlt
    have h1 := hopt y' (hxy.trans hyy')
    have h2 := hsub (y - x) (y' - y) (by linarith) (by linarith)
    rw [show y - x + (y' - y) = y' - x by ring] at h2
    linarith
  have hup : ∀ x ∈ N, ∀ x' : ℝ, x ≤ x' → x' ∈ N := by
    intro x hx x' hxx' y hy
    rcases eq_or_lt_of_le hy with rfl | hlt
    · simp [hc0]
    obtain ⟨κ, K, hκ, hKc, hline, hsupp'⟩ := hsupp (y - x') (by linarith)
    obtain ⟨-, -, a, -, I, hI, -, -, hanti, hnonK, -⟩ := hG κ hκ
    have key : κ * x' + h x' ≤ κ * y + h y + K := by
      by_cases hx'I : x' ∈ I
      · have hxI : x ∈ I := by
          rcases hI with rfl | rfl
          · exact lt_of_le_of_lt hxx' hx'I
          · exact le_trans hxx' hx'I
        have h1 : κ * x' + h x' ≤ κ * x + h x := hanti hxI hx'I hxx'
        have h2 := hx y (hxx'.trans hy)
        have h3 := hsupp' (y - x) (by linarith)
        linarith
      · have hyI : y ∉ I := by
          intro hyI'
          apply hx'I
          rcases hI with rfl | rfl
          · exact lt_of_le_of_lt hy hyI'
          · exact le_trans hy hyI'
        have h1 : κ * x' + h x' ≤ κ * y + h y + Kc c κ := hnonK x' hx'I y hyI hy
        linarith
    linarith
  have hNne : N.Nonempty := by
    obtain ⟨y, hy⟩ := hY 0
    exact ⟨y, hYN 0 y hy⟩
  have hNbdd : BddBelow N := by
    have ev := (hGtend.mono_left atBot_le_cocompact).eventually_gt_atTop (κ₀ * 0 + h 0 + K₀)
    obtain ⟨b, hb⟩ := Filter.eventually_atBot.mp ev
    refine ⟨min b 0, fun x hx => ?_⟩
    by_contra hlt
    push Not at hlt
    have hxb : x ≤ b := by linarith [min_le_left b 0]
    have hx0 : x ≤ 0 := by linarith [min_le_right b 0]
    have h1 : κ₀ * 0 + h 0 + K₀ < κ₀ * x + h x := hb x hxb
    have h2 := hx 0 hx0
    have h3 := hC₀.1.2 (0 - x) (by linarith)
    simp only at h3
    linarith
  set s := sInf N with hs
  have hgt : ∀ x : ℝ, s < x → x ∈ N := by
    intro x hx
    obtain ⟨n', hn'N, hn'x⟩ := exists_lt_of_csInf_lt hNne hx
    exact hup n' hn'N x hn'x.le
  have hsN : s ∈ N := by
    intro y hy
    rcases eq_or_lt_of_le hy with rfl | hlt
    · simp [hc0]
    have hca : ContinuousAt (fun x => c (y - x)) s := by
      have : ContinuousAt c (y - s) := hccont.continuousAt (Ioi_mem_nhds (by linarith))
      exact this.comp (continuousAt_const.sub continuousAt_id)
    have hT : Tendsto (fun x => h x - c (y - x)) (𝓝[>] s) (𝓝 (h s - c (y - s))) :=
      ((hcont.continuousAt).sub hca).tendsto.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ x in 𝓝[>] s, h x - c (y - x) ≤ h y := by
      filter_upwards [Ioo_mem_nhdsGT hlt] with x hx
      have := hgt x hx.1 y hx.2.le
      linarith
    have := le_of_tendsto hT hev
    linarith
  have hYs : ∀ x y : ℝ, y ∈ aux_gss_Y c h x → s ≤ y :=
    fun x y hy => csInf_le hNbdd (hYN x y hy)
  have hmin : ∀ x : ℝ, x < s → sInf (aux_gss_Y c h x) ∈ aux_gss_Y c h x := by
    intro x hxs
    have hne : (aux_gss_Y c h x).Nonempty := hY x
    have hbdd : BddBelow (aux_gss_Y c h x) := ⟨x, fun y hy => hy.1⟩
    set y₀ := sInf (aux_gss_Y c h x) with hy₀
    have hy₀s : s ≤ y₀ := le_csInf hne (fun y hy => hYs x y hy)
    refine ⟨by linarith, fun y hy => ?_⟩
    have hcl : y₀ ∈ closure (aux_gss_Y c h x) := csInf_mem_closure hne hbdd
    have hFcont : ContinuousAt (fun S => c (S - x) + h S) y₀ := by
      have : ContinuousAt c (y₀ - x) := hccont.continuousAt (Ioi_mem_nhds (by linarith))
      have h1 : ContinuousAt (fun S => S - x) y₀ := continuousAt_id.sub continuousAt_const
      have h2 : ContinuousAt (fun S => c (S - x)) y₀ := ContinuousAt.comp (g := c) this h1
      exact h2.add hcont.continuousAt
    have : (𝓝[aux_gss_Y c h x] y₀).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
    exact le_of_tendsto (hFcont.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall (fun S (hS : S ∈ aux_gss_Y c h x) => hS.2 y hy))
  refine ⟨s, s, fun x => if s ≤ x then x else sInf (aux_gss_Y c h x), ⟨?_, ?_, le_rfl⟩, ?_⟩
  · intro x hx
    simp only [if_pos hx]
  · intro z x hzx hxs
    have hzs : z < s := hzx.trans hxs
    simp only [if_neg (not_le.mpr hxs), if_neg (not_le.mpr hzs)]
    refine ⟨?_, hYs x _ (hmin x hxs)⟩
    by_contra hlt
    push Not at hlt
    have hyz := hmin z hzs
    have hyx := hmin x hxs
    set yz := sInf (aux_gss_Y c h z) with hyz_def
    set yx := sInf (aux_gss_Y c h x) with hyx_def
    have hyzs := hYs z yz hyz
    have hmem : yz ∈ aux_gss_Y c h x := by
      refine ⟨by linarith, fun y hy => ?_⟩
      have h1 := hyz.2 yx (by linarith [hyx.1])
      have h2 := hyx.2 y hy
      have h3 := aux_gss_four hcc (p := yz - x) (q := yz - z) (r := yx - z)
        (by linarith) (by linarith) (by linarith)
      rw [show yz - x + (yx - z) - (yz - z) = yx - x by ring] at h3
      linarith
    have := csInf_le (⟨x, fun y hy => hy.1⟩ : BddBelow (aux_gss_Y c h x)) hmem
    linarith
  · intro x
    by_cases hx : s ≤ x
    · simp only [if_pos hx]
      have hxN : x ∈ N := by
        rcases eq_or_lt_of_le hx with rfl | hlt
        · exact hsN
        · exact hgt x hlt
      refine ⟨le_rfl, fun y hy => ?_⟩
      rw [sub_self, hc0, zero_add]
      exact hxN y hy
    · simp only [if_neg hx]
      exact hmin x (not_le.mp hx)

end PorteusSS

open PorteusSS
open MeasureTheory Filter Topology Set

theorem solution (c m φ f0 : ℝ → ℝ) (α c0 K0 cInf KInf : ℝ)
    (hmodel : IsModel c m φ α c0 K0 cInf KInf) (n : ℕ) (hn : 1 ≤ n)
    (hG : ∀ κ ∈ slopeSet c, CK (Kc c κ) (Gfn c m φ f0 α κ n))
    (hY : ∀ x : ℝ, (Yset c m φ f0 α n x).Nonempty) :
    ∃ s S : ℝ, ∃ pol : ℝ → ℝ, IsGenSS pol s S ∧ ∀ x : ℝ, pol x ∈ Yset c m φ f0 α n x :=
  aux_gss_main c (hFn c m φ f0 α n) hmodel.cost.concave hmodel.cost.zero hG hY
