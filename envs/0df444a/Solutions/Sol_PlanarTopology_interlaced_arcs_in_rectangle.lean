-- Prove2me | solution 1 for PlanarTopology.interlaced_arcs_in_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T01:20:25.5347+00:00
-- url     : https://prove2.me/submissions/32a99d0b-f264-45e2-89d1-abbc67a9ccae

import Theorems.Thm_PlanarTopology_crossing_paths_in_square
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Tactic

open Set

namespace InterlacedArcs

lemma seg_coords {p q z : ℝ × ℝ} (hz : z ∈ range (Path.segment p q)) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ z.1 = p.1 + θ * (q.1 - p.1) ∧ z.2 = p.2 + θ * (q.2 - p.2) := by
  rw [Path.range_segment] at hz
  obtain ⟨u, v, hu, hv, huv, rfl⟩ := hz
  refine ⟨v, hv, by linarith, ?_, ?_⟩ <;> simp <;> rw [show u = 1 - v by linarith] <;> ring

/-- A path on `[-1,1]` from a function continuous there. -/
def toPath (Γ : ℝ → ℝ × ℝ) (hΓ : ContinuousOn Γ (Icc (-1) 1)) : Path (Γ (-1)) (Γ 1) where
  toFun t := Γ (2 * (t : ℝ) - 1)
  continuous_toFun := hΓ.comp_continuous (by fun_prop) (fun t =>
    ⟨by linarith [t.2.1], by linarith [t.2.2]⟩)
  source' := by simp
  target' := by norm_num

lemma toPath_range {Γ : ℝ → ℝ × ℝ} {hΓ : ContinuousOn Γ (Icc (-1) 1)} {z : ℝ × ℝ}
    (hz : z ∈ range (toPath Γ hΓ)) : ∃ s ∈ Icc (-1 : ℝ) 1, Γ s = z := by
  obtain ⟨t, rfl⟩ := hz
  exact ⟨2 * (t : ℝ) - 1, ⟨by linarith [t.2.1], by linarith [t.2.2]⟩, rfl⟩

lemma extend_mem_range {x y : ℝ × ℝ} (γ : Path x y) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    γ.extend ((s + 1) / 2) ∈ range γ := by
  rw [← Path.extend_range]; exact mem_range_self _


lemma seg_box {x1 x2 y1 y2 : ℝ} {p q z : ℝ × ℝ}
    (hp : x1 ≤ p.1 ∧ p.1 ≤ x2 ∧ y1 ≤ p.2 ∧ p.2 ≤ y2)
    (hq : x1 ≤ q.1 ∧ q.1 ≤ x2 ∧ y1 ≤ q.2 ∧ q.2 ≤ y2)
    (hz : z ∈ range (Path.segment p q)) :
    x1 ≤ z.1 ∧ z.1 ≤ x2 ∧ y1 ≤ z.2 ∧ z.2 ≤ y2 := by
  obtain ⟨θ, h0, h1, e1, e2⟩ := seg_coords hz
  rw [e1, e2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [mul_nonneg h0 (sub_nonneg.2 h1)]

/-- Core: after closing the configuration up to a crossing configuration in a larger square. -/
lemma core (Γ Γ' : ℝ → ℝ × ℝ) (a b h α β γ : ℝ)
    (hab : a < b) (hh : 0 < h) (hαβ : α < β) (haα : a ≤ α) (hβb : β ≤ b)
    (hγ1 : α < γ) (hγ2 : γ < β)
    (hΓ : ContinuousOn Γ (Icc (-1) 1)) (hΓ' : ContinuousOn Γ' (Icc (-1) 1))
    (hΓR : ∀ s ∈ Icc (-1 : ℝ) 1, a ≤ (Γ s).1 ∧ (Γ s).1 ≤ b ∧ 0 ≤ (Γ s).2 ∧ (Γ s).2 ≤ h)
    (hΓ'R : ∀ t ∈ Icc (-1 : ℝ) 1, a ≤ (Γ' t).1 ∧ (Γ' t).1 ≤ b ∧ 0 ≤ (Γ' t).2 ∧ (Γ' t).2 ≤ h)
    (hΓ0 : Γ (-1) = (α, 0)) (hΓ1 : Γ 1 = (β, 0)) (hΓ'0 : Γ' (-1) = (γ, 0))
    (xt : ℝ) (hxt1 : a - 1 ≤ xt) (hxt2 : xt ≤ b + 1)
    (gD : Path (Γ' 1) (xt, h + 1))
    (hgD : ∀ z ∈ range gD, z = Γ' 1 ∨
      (¬ (a ≤ z.1 ∧ z.1 ≤ b ∧ 0 ≤ z.2 ∧ z.2 ≤ h) ∧ z.2 ≠ -1 / 2 ∧ z.1 ≠ α ∧ z.1 ≠ β ∧
        a - 1 ≤ z.1 ∧ z.1 ≤ b + 1 ∧ -1 ≤ z.2 ∧ z.2 ≤ h + 1)) :
    ∃ s ∈ Icc (-1 : ℝ) 1, ∃ t ∈ Icc (-1 : ℝ) 1, Γ s = Γ' t := by
  -- the two closed-up paths
  set P1 : ℝ × ℝ := (a - 1, -1 / 2)
  set P2 : ℝ × ℝ := (α, -1 / 2)
  set Q2 : ℝ × ℝ := (β, -1 / 2)
  set Q1 : ℝ × ℝ := (b + 1, -1 / 2)
  set fP : Path P1 Q1 := (Path.segment P1 P2).trans ((Path.segment P2 (Γ (-1))).trans
    ((toPath Γ hΓ).trans ((Path.segment (Γ 1) Q2).trans (Path.segment Q2 Q1)))) with hfP
  set gP : Path ((γ, -1) : ℝ × ℝ) (xt, h + 1) :=
    (Path.segment ((γ, -1) : ℝ × ℝ) (Γ' (-1))).trans ((toPath Γ' hΓ').trans gD) with hgP
  -- the big box
  have hBf : ∀ z ∈ range fP, a - 1 ≤ z.1 ∧ z.1 ≤ b + 1 ∧ -1 ≤ z.2 ∧ z.2 ≤ h + 1 := by
    intro z hz
    simp only [hfP, Path.trans_range, mem_union] at hz
    have hR0 := hΓR (-1) ⟨le_rfl, by norm_num⟩
    have hR1 := hΓR 1 ⟨by norm_num, le_rfl⟩
    rcases hz with hz | hz | hz | hz | hz
    · exact seg_box (by simp only [P1]; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith) (by simp only [P2]; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith) hz
    · exact seg_box (by simp only [P2]; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith)
        ⟨by linarith [hR0.1], by linarith [hR0.2.1], by linarith [hR0.2.2.1], by linarith [hR0.2.2.2]⟩ hz
    · obtain ⟨s, hs, rfl⟩ := toPath_range hz
      have := hΓR s hs
      exact ⟨by linarith [this.1], by linarith [this.2.1], by linarith [this.2.2.1], by linarith [this.2.2.2]⟩
    · exact seg_box ⟨by linarith [hR1.1], by linarith [hR1.2.1], by linarith [hR1.2.2.1], by linarith [hR1.2.2.2]⟩
        (by simp only [Q2]; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith) hz
    · exact seg_box (by simp only [Q2]; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith) (by simp only [Q1]; refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith) hz
  have hBg : ∀ z ∈ range gP, a - 1 ≤ z.1 ∧ z.1 ≤ b + 1 ∧ -1 ≤ z.2 ∧ z.2 ≤ h + 1 := by
    intro z hz
    simp only [hgP, Path.trans_range, mem_union] at hz
    have hR0 := hΓ'R (-1) ⟨le_rfl, by norm_num⟩
    have hR1 := hΓ'R 1 ⟨by norm_num, le_rfl⟩
    rcases hz with hz | hz | hz
    · exact seg_box (by refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith)
        ⟨by linarith [hR0.1], by linarith [hR0.2.1], by linarith [hR0.2.2.1], by linarith [hR0.2.2.2]⟩ hz
    · obtain ⟨s, hs, rfl⟩ := toPath_range hz
      have := hΓ'R s hs
      exact ⟨by linarith [this.1], by linarith [this.2.1], by linarith [this.2.2.1], by linarith [this.2.2.2]⟩
    · rcases hgD z hz with h1 | h1
      · rw [h1]; exact ⟨by linarith [hR1.1], by linarith [hR1.2.1], by linarith [hR1.2.2.1], by linarith [hR1.2.2.2]⟩
      · exact h1.2.2.2.2
  -- normalisation to the square `[-1,1]^2`
  set T : ℝ × ℝ → ℝ × ℝ := fun z => (2 * (z.1 - (a - 1)) / (b - a + 2) - 1, 2 * (z.2 + 1) / (h + 2) - 1)
    with hT
  have hw : 0 < b - a + 2 := by linarith
  have hw' : 0 < h + 2 := by linarith
  have hTc : Continuous T := by simp only [hT]; fun_prop
  have hTbox : ∀ z : ℝ × ℝ, a - 1 ≤ z.1 ∧ z.1 ≤ b + 1 ∧ -1 ≤ z.2 ∧ z.2 ≤ h + 1 →
      |(T z).1| ≤ 1 ∧ |(T z).2| ≤ 1 := by
    intro z hz
    simp only [hT]
    constructor <;> rw [abs_le] <;> constructor <;>
      first
      | (rw [le_sub_iff_add_le, le_div_iff₀ (by assumption)]; nlinarith)
      | (rw [sub_le_iff_le_add, div_le_iff₀ (by assumption)]; nlinarith)
  have hTinj : ∀ z w : ℝ × ℝ, T z = T w → z = w := by
    intro z w hzw
    simp only [hT, Prod.mk.injEq] at hzw
    obtain ⟨h1, h2⟩ := hzw
    have e1 : 2 * (z.1 - (a - 1)) / (b - a + 2) = 2 * (w.1 - (a - 1)) / (b - a + 2) := by linarith
    have e2 : 2 * (z.2 + 1) / (h + 2) = 2 * (w.2 + 1) / (h + 2) := by linarith
    rw [div_left_inj' hw.ne'] at e1
    rw [div_left_inj' hw'.ne'] at e2
    exact Prod.ext (by linarith) (by linarith)
  set F : ℝ → ℝ × ℝ := fun s => T (fP.extend ((s + 1) / 2)) with hF
  set G : ℝ → ℝ × ℝ := fun t => T (gP.extend ((t + 1) / 2)) with hG
  obtain ⟨s, hs, t, ht, hst⟩ := PlanarTopology.crossing_paths_in_square F G
    (by simp only [hF]; exact (hTc.comp (fP.continuous_extend.comp (by fun_prop))).continuousOn)
    (by simp only [hG]; exact (hTc.comp (gP.continuous_extend.comp (by fun_prop))).continuousOn)
    (fun s hs => hTbox _ (hBf _ (extend_mem_range fP hs)))
    (fun t ht => hTbox _ (hBg _ (extend_mem_range gP ht)))
    (by simp [hF, hT, P1])
    (by simp only [hF, hT]; norm_num; field_simp; ring)
    (by simp [hG, hT])
    (by simp only [hG, hT]; norm_num; field_simp; ring)
  have hp := hTinj _ _ hst
  set p := fP.extend ((s + 1) / 2)
  have hpf : p ∈ range fP := extend_mem_range fP hs
  have hpg : p ∈ range gP := by rw [hp]; exact extend_mem_range gP ht
  -- analysis of the common point
  simp only [hfP, Path.trans_range, mem_union] at hpf
  simp only [hgP, Path.trans_range, mem_union] at hpg
  have hm1 : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hp1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hΓ'1R := hΓ'R 1 hp1
  -- coordinates on the added segments
  have cP12 : p ∈ range (Path.segment P1 P2) → p.2 = -1 / 2 ∧ p.1 ≤ α := by
    intro hz; obtain ⟨θ, h0, h1, e1, e2⟩ := seg_coords hz
    simp only [P1, P2] at e1 e2; constructor <;> nlinarith
  have cP2 : p ∈ range (Path.segment P2 (Γ (-1))) → p.1 = α ∧ -1 / 2 ≤ p.2 ∧ p.2 ≤ 0 := by
    intro hz; obtain ⟨θ, h0, h1, e1, e2⟩ := seg_coords hz
    simp only [P2, hΓ0] at e1 e2; refine ⟨?_, ?_, ?_⟩ <;> nlinarith
  have cQ2 : p ∈ range (Path.segment (Γ 1) Q2) → p.1 = β ∧ -1 / 2 ≤ p.2 ∧ p.2 ≤ 0 := by
    intro hz; obtain ⟨θ, h0, h1, e1, e2⟩ := seg_coords hz
    simp only [Q2, hΓ1] at e1 e2; refine ⟨?_, ?_, ?_⟩ <;> nlinarith
  have cQ12 : p ∈ range (Path.segment Q2 Q1) → p.2 = -1 / 2 ∧ β ≤ p.1 := by
    intro hz; obtain ⟨θ, h0, h1, e1, e2⟩ := seg_coords hz
    simp only [Q1, Q2] at e1 e2; constructor <;> nlinarith
  have cV : p ∈ range (Path.segment ((γ, -1) : ℝ × ℝ) (Γ' (-1))) → p.1 = γ ∧ p.2 ≤ 0 := by
    intro hz; obtain ⟨θ, h0, h1, e1, e2⟩ := seg_coords hz
    simp only [hΓ'0] at e1 e2; constructor <;> nlinarith
  have eα : ∀ q : ℝ × ℝ, q.1 = α → q.2 = 0 → q = Γ (-1) := fun q h1 h2 => by
    rw [hΓ0]; exact Prod.ext h1 h2
  have eβ : ∀ q : ℝ × ℝ, q.1 = β → q.2 = 0 → q = Γ 1 := fun q h1 h2 => by
    rw [hΓ1]; exact Prod.ext h1 h2
  rcases hpg with hg | hg | hg
  · -- the vertical segment below the start of `Γ'`
    obtain ⟨gx, gy⟩ := cV hg
    rcases hpf with hf | hf | hf | hf | hf
    · linarith [(cP12 hf).2]
    · linarith [(cP2 hf).1]
    · obtain ⟨s', hs', hps⟩ := toPath_range hf
      have hR := hΓR s' hs'
      rw [hps] at hR
      refine ⟨s', hs', -1, hm1, ?_⟩
      rw [hps, hΓ'0]; exact Prod.ext gx (by linarith [hR.2.2.1])
    · linarith [(cQ2 hf).1]
    · linarith [(cQ12 hf).2]
  · -- a genuine point of `Γ'`
    obtain ⟨t', ht', hpt⟩ := toPath_range hg
    have hR := hΓ'R t' ht'
    rw [hpt] at hR
    rcases hpf with hf | hf | hf | hf | hf
    · linarith [(cP12 hf).1, hR.2.2.1]
    · obtain ⟨e1, _, e3⟩ := cP2 hf
      exact ⟨-1, hm1, t', ht', by rw [hpt, ← eα p e1 (by linarith [hR.2.2.1])]⟩
    · obtain ⟨s', hs', hps⟩ := toPath_range hf
      exact ⟨s', hs', t', ht', by rw [hps, hpt]⟩
    · obtain ⟨e1, _, e3⟩ := cQ2 hf
      exact ⟨1, hp1, t', ht', by rw [hpt, ← eβ p e1 (by linarith [hR.2.2.1])]⟩
    · linarith [(cQ12 hf).1, hR.2.2.1]
  · -- the escape path from the end of `Γ'`
    rcases hgD p hg with hD | ⟨hnR, hy, hxα, hxβ, -⟩
    · rw [hD] at hpf
      rcases hpf with hf | hf | hf | hf | hf
      · have := cP12 (hD ▸ hf); rw [hD] at this; linarith [hΓ'1R.2.2.1]
      · obtain ⟨e1, _, e3⟩ := cP2 (hD ▸ hf)
        rw [hD] at e1 e3
        exact ⟨-1, hm1, 1, hp1, (eα _ e1 (by linarith [hΓ'1R.2.2.1])).symm⟩
      · obtain ⟨s', hs', hps⟩ := toPath_range hf
        exact ⟨s', hs', 1, hp1, hps⟩
      · obtain ⟨e1, _, e3⟩ := cQ2 (hD ▸ hf)
        rw [hD] at e1 e3
        exact ⟨1, hp1, 1, hp1, (eβ _ e1 (by linarith [hΓ'1R.2.2.1])).symm⟩
      · have := cQ12 (hD ▸ hf); rw [hD] at this; linarith [hΓ'1R.2.2.1]
    · exfalso
      rcases hpf with hf | hf | hf | hf | hf
      · exact hy (cP12 hf).1
      · exact hxα (cP2 hf).1
      · obtain ⟨s', hs', hps⟩ := toPath_range hf
        exact hnR (hps ▸ hΓR s' hs')
      · exact hxβ (cQ2 hf).1
      · exact hy (cQ12 hf).1

set_option maxHeartbeats 2000000 in
theorem interlaced_main (Γ Γ' : ℝ → ℝ × ℝ) (a b h α β γ : ℝ)
    (hab : a < b) (hh : 0 < h) (hαβ : α < β) (haα : a ≤ α) (hβb : β ≤ b)
    (hγ1 : α < γ) (hγ2 : γ < β)
    (hΓ : ContinuousOn Γ (Icc (-1) 1)) (hΓ' : ContinuousOn Γ' (Icc (-1) 1))
    (hΓR : ∀ s ∈ Icc (-1 : ℝ) 1, a ≤ (Γ s).1 ∧ (Γ s).1 ≤ b ∧ 0 ≤ (Γ s).2 ∧ (Γ s).2 ≤ h)
    (hΓ'R : ∀ t ∈ Icc (-1 : ℝ) 1, a ≤ (Γ' t).1 ∧ (Γ' t).1 ≤ b ∧ 0 ≤ (Γ' t).2 ∧ (Γ' t).2 ≤ h)
    (hΓ0 : Γ (-1) = (α, 0)) (hΓ1 : Γ 1 = (β, 0)) (hΓ'0 : Γ' (-1) = (γ, 0))
    (hend : (Γ' 1).1 = a ∨ (Γ' 1).1 = b ∨
      ((Γ' 1).2 = 0 ∧ ((Γ' 1).1 < α ∨ β < (Γ' 1).1))) :
    ∃ s ∈ Icc (-1 : ℝ) 1, ∃ t ∈ Icc (-1 : ℝ) 1, Γ s = Γ' t := by
  have hD := hΓ'R 1 ⟨by norm_num, le_rfl⟩
  set D := Γ' 1 with hDdef
  have core' := core Γ Γ' a b h α β γ hab hh hαβ haα hβb hγ1 hγ2 hΓ hΓ' hΓR hΓ'R hΓ0 hΓ1 hΓ'0
  rcases hend with hx | hx | ⟨hy, hx | hx⟩
  · -- the end lies on the left side: escape to the left, then up
    set E1 : ℝ × ℝ := (a - 1 / 2, D.2)
    refine core' (a - 1 / 2) (by linarith) (by linarith)
      ((Path.segment D E1).trans (Path.segment E1 (a - 1 / 2, h + 1))) ?_
    intro z hz
    rw [Path.trans_range, mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨θ, h0, h1, e1, e2⟩ := seg_coords hz
      simp only [E1] at e1 e2
      rcases eq_or_lt_of_le h0 with hθ | hθ
      · left; rw [← hθ] at e1 e2; exact Prod.ext (by simpa using e1) (by simpa using e2)
      · right
        refine ⟨fun hR => by nlinarith [hR.1], by nlinarith [hD.2.2.1], by nlinarith, by nlinarith,
          by nlinarith, by nlinarith, by nlinarith [hD.2.2.1], by nlinarith [hD.2.2.2]⟩
    · obtain ⟨θ, h0, h1, e1, e2⟩ := seg_coords hz
      simp only [E1] at e1 e2
      right
      refine ⟨fun hR => by nlinarith [hR.1], by nlinarith [hD.2.2.1, mul_nonneg h0 (sub_nonneg.2 h1)],
        by nlinarith, by nlinarith, by nlinarith, by nlinarith,
        by nlinarith [hD.2.2.1, mul_nonneg h0 (sub_nonneg.2 h1)],
        by nlinarith [hD.2.2.2, mul_nonneg h0 (sub_nonneg.2 h1)]⟩
  · -- the end lies on the right side: escape to the right, then up
    set E1 : ℝ × ℝ := (b + 1 / 2, D.2)
    refine core' (b + 1 / 2) (by linarith) (by linarith)
      ((Path.segment D E1).trans (Path.segment E1 (b + 1 / 2, h + 1))) ?_
    intro z hz
    rw [Path.trans_range, mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨θ, h0, h1, e1, e2⟩ := seg_coords hz
      simp only [E1] at e1 e2
      rcases eq_or_lt_of_le h0 with hθ | hθ
      · left; rw [← hθ] at e1 e2; exact Prod.ext (by simpa using e1) (by simpa using e2)
      · right
        refine ⟨fun hR => by nlinarith [hR.2.1], by nlinarith [hD.2.2.1], by nlinarith, by nlinarith,
          by nlinarith, by nlinarith, by nlinarith [hD.2.2.1], by nlinarith [hD.2.2.2]⟩
    · obtain ⟨θ, h0, h1, e1, e2⟩ := seg_coords hz
      simp only [E1] at e1 e2
      right
      refine ⟨fun hR => by nlinarith [hR.2.1], by nlinarith [hD.2.2.1, mul_nonneg h0 (sub_nonneg.2 h1)],
        by nlinarith, by nlinarith, by nlinarith, by nlinarith,
        by nlinarith [hD.2.2.1, mul_nonneg h0 (sub_nonneg.2 h1)],
        by nlinarith [hD.2.2.2, mul_nonneg h0 (sub_nonneg.2 h1)]⟩
  · -- the end lies on the bottom, left of `Γ`: dip down, go left, then up
    set E1 : ℝ × ℝ := (D.1, -1 / 4)
    set E2 : ℝ × ℝ := (a - 1 / 2, -1 / 4)
    refine core' (a - 1 / 2) (by linarith) (by linarith)
      ((Path.segment D E1).trans ((Path.segment E1 E2).trans (Path.segment E2 (a - 1 / 2, h + 1)))) ?_
    intro z hz
    simp only [Path.trans_range, mem_union] at hz
    rcases hz with hz | hz | hz
    · obtain ⟨θ, h0, h1, e1, e2⟩ := seg_coords hz
      simp only [E1] at e1 e2
      rcases eq_or_lt_of_le h0 with hθ | hθ
      · left; rw [← hθ] at e1 e2; exact Prod.ext (by simpa using e1) (by simpa using e2)
      · right
        refine ⟨fun hR => by nlinarith [hR.2.2.1], by nlinarith, by nlinarith, by nlinarith,
          by nlinarith [hD.1], by nlinarith [hD.2.1], by nlinarith, by nlinarith⟩
    · obtain ⟨θ, h0, h1, e1, e2⟩ := seg_coords hz
      simp only [E1, E2] at e1 e2
      right
      refine ⟨fun hR => by nlinarith [hR.2.2.1], by nlinarith,
        by nlinarith [mul_nonneg h0 (sub_nonneg.2 h1), hD.1],
        by nlinarith [mul_nonneg h0 (sub_nonneg.2 h1), hD.1],
        by nlinarith [hD.1], by nlinarith [hD.2.1], by nlinarith, by nlinarith⟩
    · obtain ⟨θ, h0, h1, e1, e2⟩ := seg_coords hz
      simp only [E2] at e1 e2
      right
      refine ⟨fun hR => by nlinarith [hR.1], by nlinarith, by nlinarith, by nlinarith,
        by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · -- the end lies on the bottom, right of `Γ`: dip down, go right, then up
    set E1 : ℝ × ℝ := (D.1, -1 / 4)
    set E2 : ℝ × ℝ := (b + 1 / 2, -1 / 4)
    refine core' (b + 1 / 2) (by linarith) (by linarith)
      ((Path.segment D E1).trans ((Path.segment E1 E2).trans (Path.segment E2 (b + 1 / 2, h + 1)))) ?_
    intro z hz
    simp only [Path.trans_range, mem_union] at hz
    rcases hz with hz | hz | hz
    · obtain ⟨θ, h0, h1, e1, e2⟩ := seg_coords hz
      simp only [E1] at e1 e2
      rcases eq_or_lt_of_le h0 with hθ | hθ
      · left; rw [← hθ] at e1 e2; exact Prod.ext (by simpa using e1) (by simpa using e2)
      · right
        refine ⟨fun hR => by nlinarith [hR.2.2.1], by nlinarith, by nlinarith, by nlinarith,
          by nlinarith [hD.1], by nlinarith [hD.2.1], by nlinarith, by nlinarith⟩
    · obtain ⟨θ, h0, h1, e1, e2⟩ := seg_coords hz
      simp only [E1, E2] at e1 e2
      right
      refine ⟨fun hR => by nlinarith [hR.2.2.1], by nlinarith,
        by nlinarith [mul_nonneg h0 (sub_nonneg.2 h1), hD.2.1],
        by nlinarith [mul_nonneg h0 (sub_nonneg.2 h1), hD.2.1],
        by nlinarith [hD.1], by nlinarith [hD.2.1], by nlinarith, by nlinarith⟩
    · obtain ⟨θ, h0, h1, e1, e2⟩ := seg_coords hz
      simp only [E2] at e1 e2
      right
      refine ⟨fun hR => by nlinarith [hR.2.1], by nlinarith, by nlinarith, by nlinarith,
        by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

end InterlacedArcs

theorem solution (Γ Γ' : ℝ → ℝ × ℝ) (a b h α β γ : ℝ)
    (hab : a < b) (hh : 0 < h) (hαβ : α < β) (haα : a ≤ α) (hβb : β ≤ b)
    (hγ1 : α < γ) (hγ2 : γ < β)
    (hΓ : ContinuousOn Γ (Set.Icc (-1) 1)) (hΓ' : ContinuousOn Γ' (Set.Icc (-1) 1))
    (hΓR : ∀ s ∈ Set.Icc (-1 : ℝ) 1,
      a ≤ (Γ s).1 ∧ (Γ s).1 ≤ b ∧ 0 ≤ (Γ s).2 ∧ (Γ s).2 ≤ h)
    (hΓ'R : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      a ≤ (Γ' t).1 ∧ (Γ' t).1 ≤ b ∧ 0 ≤ (Γ' t).2 ∧ (Γ' t).2 ≤ h)
    (hΓ0 : Γ (-1) = (α, 0)) (hΓ1 : Γ 1 = (β, 0)) (hΓ'0 : Γ' (-1) = (γ, 0))
    (hend : (Γ' 1).1 = a ∨ (Γ' 1).1 = b ∨
      ((Γ' 1).2 = 0 ∧ ((Γ' 1).1 < α ∨ β < (Γ' 1).1))) :
    ∃ s ∈ Set.Icc (-1 : ℝ) 1, ∃ t ∈ Set.Icc (-1 : ℝ) 1, Γ s = Γ' t :=
  InterlacedArcs.interlaced_main Γ Γ' a b h α β γ hab hh hαβ haα hβb hγ1 hγ2 hΓ hΓ' hΓR hΓ'R
    hΓ0 hΓ1 hΓ'0 hend
