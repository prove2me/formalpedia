-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P26.translatedCone_pointed_criteria
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T02:50:23.813524+00:00
-- url     : https://prove2.me/submissions/5db12dbd-a813-43e1-a6d5-14772bc150f0

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P26

open Set Filter Topology

namespace G53TC
open QAlgorithms.Papers.Independent.Frontier30.P26

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma rec_of_cone {D : Set E} (hD : ClosedCone D) : recession D = D := by
  ext v; constructor
  · intro hv; simpa using hv 0 hD.2.2.1
  · intro hv d hd
    have := hD.2.1 hd hv (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    have h2 := hD.2.2.2 2 (by norm_num) _ this
    convert h2 using 1
    rw [smul_add, smul_smul, smul_smul]; norm_num

lemma pointed_cone_iff {D : Set E} (hD : ClosedCone D) :
    QAlgorithms.Papers.Independent.Frontier30.P26.Pointed D ↔ ∀ v ∈ D, -v ∈ D → v = 0 := by
  unfold QAlgorithms.Papers.Independent.Frontier30.P26.Pointed; rw [rec_of_cone hD]

def S (x : E) (C : Set E) : Set E := setSum {y | ∃ t : ℝ, 0 ≤ t ∧ y = t • x} C

lemma mem_S {x : E} {C : Set E} {y : E} : y ∈ S x C ↔ ∃ t : ℝ, 0 ≤ t ∧ ∃ c ∈ C, y = t • x + c := by
  unfold S setSum; constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, c, hc, rfl⟩; exact ⟨t, ht, c, hc, rfl⟩
  · rintro ⟨t, ht, c, hc, rfl⟩; exact ⟨_, ⟨t, ht, rfl⟩, c, hc, rfl⟩

lemma S_closedCone {x : E} {C : Set E} (hC : ClosedCone C) : ClosedCone (closure (S x C)) := by
  have hconv : Convex ℝ (S x C) := by
    intro y hy z hz a b ha hb hab
    obtain ⟨t, ht, c, hc, rfl⟩ := mem_S.mp hy
    obtain ⟨t', ht', c', hc', rfl⟩ := mem_S.mp hz
    refine mem_S.mpr ⟨a * t + b * t', by positivity, a • c + b • c', hC.2.1 hc hc' ha hb hab, ?_⟩
    simp only [smul_add, smul_smul, add_smul]; abel
  refine ⟨isClosed_closure, hconv.closure, subset_closure (mem_S.mpr ⟨0, le_rfl, 0, hC.2.2.1, by simp⟩), ?_⟩
  intro r hr y hy
  have hmaps : MapsTo (fun y : E => r • y) (S x C) (S x C) := by
    intro y hy
    obtain ⟨t, ht, c, hc, rfl⟩ := mem_S.mp hy
    exact mem_S.mpr ⟨r * t, mul_nonneg hr ht, r • c, hC.2.2.2 r hr c hc, by
      show r • (t • x + c) = _; rw [smul_add, smul_smul]⟩
  exact map_mem_closure (continuous_const_smul r) hy hmaps

lemma hull_eq {x : E} {C : Set E} (hC : ClosedCone C) :
    closedConeHull (translatedSubset x C) = closure (S x C) := by
  apply le_antisymm
  · apply sInter_subset_of_mem
    refine ⟨S_closedCone hC, ?_⟩
    rintro _ ⟨c, hc, rfl⟩
    exact subset_closure (mem_S.mpr ⟨1, zero_le_one, c, hc, by simp⟩)
  · apply subset_sInter
    rintro D ⟨hD, hsub⟩
    apply closure_minimal _ hD.1
    intro y hy
    obtain ⟨t, ht, c, hc, rfl⟩ := mem_S.mp hy
    rcases ht.eq_or_lt with h0 | hpos
    · rw [← h0, zero_smul, zero_add]
      -- c = lim (1/(n+1)) • (x + (n+1) • c)
      have hmem : ∀ n : ℕ, ((n : ℝ) + 1)⁻¹ • x + c ∈ D := by
        intro n
        have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have h1 : x + ((n : ℝ) + 1) • c ∈ D := hsub ⟨_, hC.2.2.2 _ hpos.le c hc, rfl⟩
        have h2 := hD.2.2.2 _ (inv_nonneg.mpr hpos.le) _ h1
        convert h2 using 1
        rw [smul_add, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
      have hlim : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • x + c) atTop (𝓝 ((0:ℝ) • x + c)) := by
        apply Tendsto.add _ tendsto_const_nhds
        apply Tendsto.smul_const
        exact tendsto_one_div_add_atTop_nhds_zero_nat.congr (fun n => by simp)
      rw [zero_smul, zero_add] at hlim
      exact hD.1.mem_of_tendsto hlim (Eventually.of_forall hmem)
    · have h1 : x + t⁻¹ • c ∈ D := hsub ⟨_, hC.2.2.2 _ (inv_nonneg.mpr hpos.le) c hc, rfl⟩
      have h2 := hD.2.2.2 t hpos.le _ h1
      convert h2 using 1
      rw [smul_add, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

lemma closure_S_sub {x : E} {C : Set E} (hC : ClosedCone C) (hx : -x ∉ C) :
    closure (S x C) ⊆ S x C := by
  intro v hv
  obtain ⟨u, huS, hu⟩ := mem_closure_iff_seq_limit.mp hv
  choose a ha c hc hu' using fun n => mem_S.mp (huS n)
  have hb : ∀ n, a n / (1 + a n) ∈ Icc (0:ℝ) 1 := fun n =>
    ⟨div_nonneg (ha n) (by linarith [ha n]), (div_le_one (by linarith [ha n])).mpr (by linarith)⟩
  obtain ⟨b, hb1, φ, hφ, hbφ⟩ := isCompact_Icc.tendsto_subseq hb
  have huφ : Tendsto (u ∘ φ) atTop (𝓝 v) := hu.comp hφ.tendsto_atTop
  have hpos : ∀ n, 0 < 1 + a n := fun n => by linarith [ha n]
  rcases hb1.2.lt_or_eq with hlt | heq
  · -- a (φ n) → b / (1 - b)
    have ha_eq : ∀ n, a n = (a n / (1 + a n)) / (1 - a n / (1 + a n)) := by
      intro n
      have := hpos n
      field_simp
      ring
    have haφ : Tendsto (fun n => a (φ n)) atTop (𝓝 (b / (1 - b))) := by
      have := hbφ.div ((tendsto_const_nhds (x := (1:ℝ))).sub hbφ) (by linarith)
      exact this.congr (fun n => (ha_eq (φ n)).symm)
    have hcφ : Tendsto (fun n => u (φ n) - a (φ n) • x) atTop (𝓝 (v - (b / (1 - b)) • x)) :=
      huφ.sub (haφ.smul_const x)
    have hmem : v - (b / (1 - b)) • x ∈ C := by
      apply hC.1.mem_of_tendsto hcφ (Eventually.of_forall fun n => ?_)
      rw [hu' (φ n)]; simpa using hc (φ n)
    have hb0 : 0 ≤ b / (1 - b) := div_nonneg hb1.1 (by linarith)
    exact mem_S.mpr ⟨_, hb0, _, hmem, by abel⟩
  · exfalso; apply hx
    -- (1/(1+a)) u → 0 ; and (1/(1+a)) u = (a/(1+a)) x + (1/(1+a)) c
    have hinv : Tendsto (fun n => (1 + a (φ n))⁻¹) atTop (𝓝 0) := by
      have : Tendsto (fun n => 1 - a (φ n) / (1 + a (φ n))) atTop (𝓝 (1 - b)) :=
        tendsto_const_nhds.sub hbφ
      rw [heq, sub_self] at this
      exact this.congr (fun n => by have := hpos (φ n); field_simp; ring)
    have h1 : Tendsto (fun n => (1 + a (φ n))⁻¹ • u (φ n) - (a (φ n) / (1 + a (φ n))) • x) atTop
        (𝓝 ((0:ℝ) • v - b • x)) := (hinv.smul huφ).sub (hbφ.smul_const x)
    rw [zero_smul, zero_sub, heq, one_smul] at h1
    apply hC.1.mem_of_tendsto h1 (Eventually.of_forall fun n => ?_)
    have e : (1 + a (φ n))⁻¹ • u (φ n) - (a (φ n) / (1 + a (φ n))) • x = (1 + a (φ n))⁻¹ • c (φ n) := by
      rw [hu' (φ n), smul_add, smul_smul, div_eq_inv_mul]; abel
    rw [e]
    exact hC.2.2.2 _ (inv_nonneg.mpr (hpos _).le) _ (hc _)

end G53TC

noncomputable section
open Set
open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Frontier30 QAlgorithms.Papers.Independent.Frontier30.P26
open QAlgorithms.Papers.Independent.Dependency50.P12.Coordinates (expAd)
attribute [local instance 100] LieRing.ofAssociativeRing
section Geometry
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem solution [FiniteDimensional ℝ E] (C : Set E) (x : E)
    (hc : ClosedCone C) (hp : Pointed C) :
    closedConeHull (translatedSubset x C) = closure (setSum {y | ∃ t : ℝ, 0 ≤ t ∧ y = t • x} C) ∧
    (Pointed (closedConeHull (translatedSubset x C)) ↔ translatedSubset x C ∩ (Neg.neg '' C) ⊆ ({0} : Set E)) ∧
    (Pointed (closedConeHull (translatedSubset x C)) ↔ (0 : E) ∉ translatedSubset x C ∨ x = 0) := by
  have hK := G53TC.hull_eq (x := x) hc
  have hKc : ClosedCone (closure (G53TC.S x C)) := G53TC.S_closedCone hc
  have hpC := (G53TC.pointed_cone_iff hc).mp hp
  have h0iff : (0 : E) ∈ translatedSubset x C ↔ -x ∈ C := by
    constructor
    · rintro ⟨c, hc', hxc⟩
      have : c = -x := by simp only at hxc; rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact hxc
      rwa [← this]
    · intro h; exact ⟨-x, h, by simp⟩
  have P3 : Pointed (closedConeHull (translatedSubset x C)) ↔ (0 : E) ∉ translatedSubset x C ∨ x = 0 := by
    rw [hK, G53TC.pointed_cone_iff hKc, h0iff]
    constructor
    · intro H
      by_contra hcon
      push Not at hcon
      obtain ⟨hnx, hx0⟩ := hcon
      apply hx0
      apply H
      · exact subset_closure (G53TC.mem_S.mpr ⟨1, zero_le_one, 0, hc.2.2.1, by simp⟩)
      · exact subset_closure (G53TC.mem_S.mpr ⟨0, le_rfl, -x, hnx, by simp⟩)
    · rintro (hnx | rfl) v hv hnv
      · have hsub := G53TC.closure_S_sub hc hnx
        obtain ⟨a, ha, c1, hc1, rfl⟩ := G53TC.mem_S.mp (hsub hv)
        obtain ⟨b, hb, c2, hc2, hc2e⟩ := G53TC.mem_S.mp (hsub hnv)
        have hsum : (a + b) • x + (c1 + c2) = 0 := by
          rw [add_smul]
          have : -(a • x + c1) + (a • x + c1) = 0 := neg_add_cancel _
          rw [hc2e] at this
          rw [← this]; abel
        rcases (add_nonneg ha hb).eq_or_lt with h0 | hpos
        · have ha0 : a = 0 := by linarith
          have hb0 : b = 0 := by linarith
          rw [ha0, hb0, add_zero, zero_smul, zero_add] at hsum
          have hc12 : c2 = -c1 := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum
          rw [ha0, zero_smul, zero_add]
          exact hpC c1 hc1 (hc12 ▸ hc2)
        · exfalso; apply hnx
          have hm := hc.2.2.2 _ (inv_nonneg.mpr hpos.le) _ (hc.2.1 hc1 hc2 (by norm_num : (0:ℝ) ≤ 1/2)
            (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num))
          have hm2 := hc.2.2.2 2 (by norm_num) _ hm
          convert hm2 using 1
          have : c1 + c2 = -((a + b) • x) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum
          rw [smul_smul, smul_add, smul_smul, smul_smul, ← smul_add, this, smul_neg, smul_smul]
          field_simp
          simp
      · have hS : G53TC.S (0 : E) C = C := by
          ext y; rw [G53TC.mem_S]; constructor
          · rintro ⟨t, _, c, hc', rfl⟩; simpa using hc'
          · intro hy; exact ⟨0, le_rfl, y, hy, by simp⟩
        rw [hS, hc.1.closure_eq] at hv hnv
        exact hpC v hv hnv
  refine ⟨hK, ?_, P3⟩
  rw [P3, h0iff]
  constructor
  · intro H
    rcases H with hnx | rfl
    · rintro _ ⟨⟨c, hc1, rfl⟩, ⟨c', hc2, hc2e⟩⟩
      exfalso; apply hnx
      have : -x = c + c' := by
        simp only at hc2e
        rw [eq_comm, ← sub_eq_zero] at hc2e ⊢
        rw [← hc2e]; abel
      rw [this]
      have := hc.2.2.2 2 (by norm_num) _ (hc.2.1 hc1 hc2 (by norm_num : (0:ℝ) ≤ 1/2)
            (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num))
      convert this using 1
      rw [smul_add, smul_smul, smul_smul]; norm_num
    · rintro _ ⟨⟨c, hc1, rfl⟩, ⟨c', hc2, hc2e⟩⟩
      simp only [zero_add] at hc2e ⊢
      rw [mem_singleton_iff]
      exact hpC c hc1 (hc2e ▸ (by simpa using hc2))
  · intro H
    by_cases hnx : -x ∈ C
    · right
      have hm : x + ((1/2 : ℝ) • -x) ∈ translatedSubset x C ∩ (Neg.neg '' C) := by
        refine ⟨⟨_, hc.2.2.2 _ (by norm_num) _ hnx, rfl⟩, ⟨(1/2 : ℝ) • -x, hc.2.2.2 _ (by norm_num) _ hnx, ?_⟩⟩
        module
      have := H hm
      rw [mem_singleton_iff] at this
      have h2 : x = (2 : ℝ) • (x + ((1/2 : ℝ) • -x)) := by module
      rw [h2, this, smul_zero]
    · left; exact hnx

end Geometry
end
