-- Prove2me | solution 1 for Viterbo.viterbo_cEHZ_prod_polar_iff_mahler
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T15:55:51.645189+00:00
-- url     : https://prove2.me/submissions/ba7054a8-c6f0-483c-9fbf-59db90d1d40a

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo
import Theorems.Thm_OAI_SymmetricMahler_symmetric_mahler


namespace Viterbo.MahlerIff

open OAI.SymmetricPolar MeasureTheory Set Filter Topology
open Viterbo

/-! ## The scalar square loop -/

noncomputable def fF (s : ℝ) : ℝ := max (-1) (min 1 (max (3 - 8 * s) (8 * s - 7)))
noncomputable def fG (s : ℝ) : ℝ := max (-1) (min 1 (min (8 * s - 1) (5 - 8 * s)))

noncomputable def F (t : ℝ) : ℝ := fF (Int.fract t)
noncomputable def G (t : ℝ) : ℝ := fG (Int.fract t)

lemma fF_cont : Continuous fF := by unfold fF; fun_prop
lemma fG_cont : Continuous fG := by unfold fG; fun_prop

lemma F_cont : Continuous F :=
  fF_cont.continuousOn.comp_fract'' (by norm_num [fF])
lemma G_cont : Continuous G :=
  fG_cont.continuousOn.comp_fract'' (by norm_num [fG])

lemma abs_fF (s : ℝ) : |fF s| ≤ 1 :=
  abs_le.2 ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
lemma abs_fG (s : ℝ) : |fG s| ≤ 1 :=
  abs_le.2 ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma abs_F (t : ℝ) : |F t| ≤ 1 := abs_fF _
lemma abs_G (t : ℝ) : |G t| ≤ 1 := abs_fG _

lemma F_periodic : Function.Periodic F 1 := fun t => by simp [F, Int.fract_add_one]
lemma G_periodic : Function.Periodic G 1 := fun t => by simp [G, Int.fract_add_one]

lemma F_or_G (t : ℝ) : |F t| = 1 ∨ |G t| = 1 := by
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  simp only [F, G]
  set s := Int.fract t
  rcases le_or_gt s (1/4) with h | h
  · left; have : fF s = 1 := by
      simp only [fF, max_def, min_def]; split_ifs <;> linarith
    rw [this]; norm_num
  rcases le_or_gt s (1/2) with h' | h'
  · right; have : fG s = 1 := by
      simp only [fG, max_def, min_def]; split_ifs <;> linarith
    rw [this]; norm_num
  rcases le_or_gt s (3/4) with h'' | h''
  · left; have : fF s = -1 := by
      simp only [fF, max_def, min_def]; split_ifs <;> linarith
    rw [this]; norm_num
  · right; have : fG s = -1 := by
      simp only [fG, max_def, min_def]; split_ifs <;> linarith
    rw [this]; norm_num

lemma hasDerivAt_comp_fract {f : ℝ → ℝ} {a b m c : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hf : ∀ s ∈ Ioo a b, f s = m * s + c) (t : ℝ) (ht : Int.fract t ∈ Ioo a b) :
    HasDerivAt (fun t => f (Int.fract t)) m t := by
  set k : ℝ := (⌊t⌋ : ℝ)
  have htk : t = k + Int.fract t := (Int.floor_add_fract t).symm
  have hU : Ioo (k + a) (k + b) ∈ 𝓝 t :=
    isOpen_Ioo.mem_nhds ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have heq : (fun t' => m * t' + (c - m * k)) =ᶠ[𝓝 t] fun t => f (Int.fract t) := by
    filter_upwards [hU] with t' ht'
    have hfl : ⌊t'⌋ = ⌊t⌋ := by
      rw [Int.floor_eq_iff]
      constructor <;> linarith [ht'.1, ht'.2]
    have hfr : Int.fract t' = t' - k := by
      rw [← Int.self_sub_floor, hfl]
    rw [hfr, hf _ ⟨by linarith [ht'.1], by linarith [ht'.2]⟩]
    ring
  have hd : HasDerivAt (fun t' => m * t' + (c - m * k)) m t := by
    simpa using ((hasDerivAt_id t).const_mul m).add_const (c - m * k)
  exact hd.congr_of_eventuallyEq heq.symm

/-- The break points `k / 4`. -/
def D : Set ℝ := Set.range (fun k : ℤ => (k : ℝ) / 4)

lemma D_countable : D.Countable := Set.countable_range _

lemma fract_ne {t : ℝ} (ht : t ∉ D) (j : ℤ) : Int.fract t ≠ (j : ℝ) / 4 := by
  intro h
  apply ht
  refine ⟨4 * ⌊t⌋ + j, ?_⟩
  have := Int.floor_add_fract t
  push_cast
  rw [h] at this
  linarith

/-- Phase data off the break points. -/
lemma phase {t : ℝ} (ht : t ∉ D) : ∃ φ ψ : ℝ, HasDerivAt F φ t ∧ HasDerivAt G ψ t ∧
    ((φ = 0 ∧ ψ = 8 ∧ F t = 1) ∨ (φ = -8 ∧ ψ = 0 ∧ G t = 1) ∨
      (φ = 0 ∧ ψ = -8 ∧ F t = -1) ∨ (φ = 8 ∧ ψ = 0 ∧ G t = -1)) := by
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  have n0 := fract_ne ht 0
  have n1 := fract_ne ht 1
  have n2 := fract_ne ht 2
  have n3 := fract_ne ht 3
  push_cast at n0 n1 n2 n3
  have p0 : 0 < Int.fract t := lt_of_le_of_ne h0 (by intro h; exact n0 (by rw [← h]; ring))
  rcases lt_or_gt_of_ne n1 with q1 | q1
  · -- first quarter
    have hFq : ∀ s ∈ Ioo (0 : ℝ) (1/4), fF s = 0 * s + 1 := by
      intro s hs; obtain ⟨_, _⟩ := hs
      simp only [fF, max_def, min_def]; split_ifs <;> linarith
    have hGq : ∀ s ∈ Ioo (0 : ℝ) (1/4), fG s = 8 * s + (-1) := by
      intro s hs; obtain ⟨_, _⟩ := hs
      simp only [fG, max_def, min_def]; split_ifs <;> linarith
    have hm : Int.fract t ∈ Ioo (0 : ℝ) (1/4) := ⟨p0, by linarith⟩
    refine ⟨0, 8, hasDerivAt_comp_fract le_rfl (by norm_num) hFq t hm,
      hasDerivAt_comp_fract le_rfl (by norm_num) hGq t hm, Or.inl ⟨rfl, rfl, ?_⟩⟩
    show fF _ = 1; rw [hFq _ hm]; ring
  rcases lt_or_gt_of_ne n2 with q2 | q2
  · have hFq : ∀ s ∈ Ioo (1/4 : ℝ) (1/2), fF s = (-8) * s + 3 := by
      intro s hs; obtain ⟨_, _⟩ := hs
      simp only [fF, max_def, min_def]; split_ifs <;> linarith
    have hGq : ∀ s ∈ Ioo (1/4 : ℝ) (1/2), fG s = 0 * s + 1 := by
      intro s hs; obtain ⟨_, _⟩ := hs
      simp only [fG, max_def, min_def]; split_ifs <;> linarith
    have hm : Int.fract t ∈ Ioo (1/4 : ℝ) (1/2) := ⟨by linarith, by linarith⟩
    refine ⟨-8, 0, hasDerivAt_comp_fract (by norm_num) (by norm_num) hFq t hm,
      hasDerivAt_comp_fract (by norm_num) (by norm_num) hGq t hm, Or.inr (Or.inl ⟨rfl, rfl, ?_⟩)⟩
    show fG _ = 1; rw [hGq _ hm]; ring
  rcases lt_or_gt_of_ne n3 with q3 | q3
  · have hFq : ∀ s ∈ Ioo (1/2 : ℝ) (3/4), fF s = 0 * s + (-1) := by
      intro s hs; obtain ⟨_, _⟩ := hs
      simp only [fF, max_def, min_def]; split_ifs <;> linarith
    have hGq : ∀ s ∈ Ioo (1/2 : ℝ) (3/4), fG s = (-8) * s + 5 := by
      intro s hs; obtain ⟨_, _⟩ := hs
      simp only [fG, max_def, min_def]; split_ifs <;> linarith
    have hm : Int.fract t ∈ Ioo (1/2 : ℝ) (3/4) := ⟨by linarith, by linarith⟩
    refine ⟨0, -8, hasDerivAt_comp_fract (by norm_num) (by norm_num) hFq t hm,
      hasDerivAt_comp_fract (by norm_num) (by norm_num) hGq t hm,
      Or.inr (Or.inr (Or.inl ⟨rfl, rfl, ?_⟩))⟩
    show fF _ = -1; rw [hFq _ hm]; ring
  · have hFq : ∀ s ∈ Ioo (3/4 : ℝ) 1, fF s = 8 * s + (-7) := by
      intro s hs; obtain ⟨_, _⟩ := hs
      simp only [fF, max_def, min_def]; split_ifs <;> linarith
    have hGq : ∀ s ∈ Ioo (3/4 : ℝ) 1, fG s = 0 * s + (-1) := by
      intro s hs; obtain ⟨_, _⟩ := hs
      simp only [fG, max_def, min_def]; split_ifs <;> linarith
    have hm : Int.fract t ∈ Ioo (3/4 : ℝ) 1 := ⟨by linarith, h1⟩
    refine ⟨8, 0, hasDerivAt_comp_fract (by norm_num) le_rfl hFq t hm,
      hasDerivAt_comp_fract (by norm_num) le_rfl hGq t hm,
      Or.inr (Or.inr (Or.inr ⟨rfl, rfl, ?_⟩))⟩
    show fG _ = -1; rw [hGq _ hm]; ring

lemma F_zero : F 0 = 1 := by norm_num [F, fF]
lemma F_half : F (1/2) = -1 := by
  have : Int.fract (1/2 : ℝ) = 1/2 := Int.fract_eq_self.2 ⟨by norm_num, by norm_num⟩
  rw [F, this]; norm_num [fF]


/-! ## The loop on `∂(K × K°)` -/

section Loop

variable {n : ℕ} {K : Set (Position n)} {x y : Position n}

/-- The standing data: `x ∈ K`, `y ∈ K°`, `⟪x, y⟫ = 1`, `K` convex and symmetric. -/
structure XY (K : Set (Position n)) (x y : Position n) : Prop where
  conv : Convex ℝ K
  sym : ∀ z, z ∈ K ↔ -z ∈ K
  hx : x ∈ K
  hy : y ∈ polar K
  hxy : inner ℝ x y = 1

lemma XY.inner_le {H : XY K x y} {a : Position n} (ha : a ∈ K) :
    |inner ℝ a y| ≤ 1 := by
  have h1 := H.hy a ha
  have h2 := H.hy (-a) ((H.sym a).1 ha)
  rw [inner_neg_left] at h2
  exact abs_le.2 ⟨by linarith, h1⟩

lemma XY.inner_le' (H : XY K x y) {b : Position n} (hb : b ∈ polar K) :
    |inner ℝ x b| ≤ 1 := by
  have h1 := hb x H.hx
  have h2 := hb (-x) ((H.sym x).1 H.hx)
  rw [inner_neg_left] at h2
  exact abs_le.2 ⟨by linarith, h1⟩

lemma XY.smul_x (H : XY K x y) {a : ℝ} (ha : |a| ≤ 1) : a • x ∈ K := by
  obtain ⟨h1, h2⟩ := abs_le.1 ha
  have := H.conv H.hx ((H.sym x).1 H.hx) (show 0 ≤ (1 + a) / 2 by linarith)
    (show 0 ≤ (1 - a) / 2 by linarith) (by ring)
  convert this using 1
  module

lemma XY.smul_y (H : XY K x y) {b : ℝ} (hb : |b| ≤ 1) : b • y ∈ polar K := by
  intro q hq
  rw [inner_smul_right]
  calc b * inner ℝ q y ≤ |b * inner ℝ q y| := le_abs_self _
    _ = |b| * |inner ℝ q y| := abs_mul _ _
    _ ≤ 1 := mul_le_one₀ hb (abs_nonneg _) (XY.inner_le (H := H) hq)

lemma XY.frontier (H : XY K x y) {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hab : |a| = 1 ∨ |b| = 1) : ((a • x, b • y) : Phase n) ∈ frontier (K ×ˢ polar K) := by
  refine ⟨subset_closure ⟨H.smul_x ha, H.smul_y hb⟩, fun hint => ?_⟩
  set z : Phase n := (a • x, b • y)
  have ht : Tendsto (fun c : ℝ => c • z) (𝓝 1) (𝓝 z) := by
    have : Tendsto (fun c : ℝ => c • z) (𝓝 1) (𝓝 ((1 : ℝ) • z)) :=
      ((continuous_id.smul continuous_const).tendsto 1)
    rwa [one_smul] at this
  have hev := ((ht.eventually (isOpen_interior.mem_nhds hint)).filter_mono
    nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi (1 : ℝ)))
  obtain ⟨c, hc, hc1⟩ := hev.exists
  have hcS := interior_subset hc
  obtain ⟨hc1', hc2'⟩ := hcS
  simp only [z, Prod.smul_mk, smul_smul] at hc1' hc2'
  have hc1 : (1 : ℝ) < c := hc1
  rcases hab with h | h
  · have := H.smul_y ha ((c * a) • x) hc1'
    rw [inner_smul_left, inner_smul_right, H.hxy] at this
    have ha2 : a * a = 1 := by
      have := sq_abs a; rw [h] at this; nlinarith
    simp only [conj_trivial] at this
    nlinarith
  · have := hc2' (b • x) (H.smul_x hb)
    rw [inner_smul_left, inner_smul_right, H.hxy] at this
    have hb2 : b * b = 1 := by
      have := sq_abs b; rw [h] at this; nlinarith
    simp only [conj_trivial] at this
    nlinarith

noncomputable def gam (x y : Position n) (t : ℝ) : Phase n := (F t • x, G t • y)

lemma gam_deriv (x y : Position n) {t : ℝ} (ht : t ∉ D) : ∃ φ ψ : ℝ,
    HasDerivAt (gam x y) ((φ • x, ψ • y) : Phase n) t ∧
    ((φ = 0 ∧ ψ = 8 ∧ F t = 1) ∨ (φ = -8 ∧ ψ = 0 ∧ G t = 1) ∨
      (φ = 0 ∧ ψ = -8 ∧ F t = -1) ∨ (φ = 8 ∧ ψ = 0 ∧ G t = -1)) := by
  obtain ⟨φ, ψ, hF, hG, hc⟩ := phase ht
  exact ⟨φ, ψ, (hF.smul_const x).prodMk (hG.smul_const y), hc⟩

lemma XY.normal (H : XY K x y) {a b φ ψ : ℝ}
    (hc : (φ = 0 ∧ ψ = 8 ∧ a = 1) ∨ (φ = -8 ∧ ψ = 0 ∧ b = 1) ∨
      (φ = 0 ∧ ψ = -8 ∧ a = -1) ∨ (φ = 8 ∧ ψ = 0 ∧ b = -1)) :
    ((φ • x, ψ • y) : Phase n) ∈ J '' normalCone phaseInner (K ×ˢ polar K) (a • x, b • y) := by
  refine ⟨(ψ • y, -(φ • x)), ?_, by simp [J]⟩
  rintro ⟨p, q⟩ ⟨hp, hq⟩
  have hA := abs_le.1 (XY.inner_le (H := H) hp)
  have hB := abs_le.1 (H.inner_le' hq)
  have hxy := H.hxy
  simp only [phaseInner, Prod.fst_sub, Prod.snd_sub, inner_sub_right, inner_smul_left,
    inner_smul_right, inner_neg_left, conj_trivial]
  rw [real_inner_comm p y, real_inner_comm x y, hxy]
  rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    nlinarith [hA.1, hA.2, hB.1, hB.2]

lemma gam_cont (x y : Position n) : Continuous (gam x y) :=
  (F_cont.smul continuous_const).prodMk (G_cont.smul continuous_const)

lemma deriv_bound (x y : Position n) {t : ℝ} (ht : t ∉ D) :
    ‖deriv (gam x y) t‖ ≤ 8 * (‖x‖ + ‖y‖) := by
  obtain ⟨φ, ψ, hd, hc⟩ := gam_deriv x y ht
  rw [hd.deriv]
  have hφ : |φ| ≤ 8 := by
    rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  have hψ : |ψ| ≤ 8 := by
    rcases hc with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> norm_num
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  rw [norm_prod_le_iff, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  constructor <;> nlinarith [abs_nonneg φ, abs_nonneg ψ]

lemma gam_loc (x y : Position n) : LocallyIntegrable (deriv (gam x y)) volume := by
  rw [locallyIntegrable_iff]
  intro k hk
  exact Measure.integrableOn_of_bounded hk.measure_lt_top.ne
    (stronglyMeasurable_deriv _).aestronglyMeasurable
    (ae_restrict_of_ae ((D_countable.ae_notMem volume).mono fun t ht => deriv_bound x y ht))

lemma gam_periodic (x y : Position n) : Function.Periodic (gam x y) 1 := by
  intro t; simp only [gam, F_periodic t, G_periodic t]

lemma XY.gcc (H : XY K x y) :
    IsGeneralizedClosedCharacteristic (K ×ˢ polar K) (gam x y) := by
  refine ⟨gam_periodic x y, fun t => H.frontier (abs_F t) (abs_G t) (F_or_G t),
    deriv (gam x y), gam_loc x y, ?_, ?_⟩
  · intro a b
    rw [integral_eq_of_hasDerivAt_off_countable _ _ D_countable (gam_cont x y).continuousOn
      (fun t ht => ?_) ((gam_loc x y).integrableOn_isCompact isCompact_uIcc).intervalIntegrable]
    obtain ⟨φ, ψ, hd, -⟩ := gam_deriv x y ht.2
    rw [hd.deriv]; exact hd
  · filter_upwards [D_countable.ae_notMem volume] with t ht
    obtain ⟨φ, ψ, hd, hc⟩ := gam_deriv x y ht
    rw [hd.deriv]
    exact H.normal hc

lemma XY.action_eq (H : XY K x y) : action (gam x y) = 4 := by
  unfold action
  have : ∫ t in (0 : ℝ)..1, phaseInner (J (gam x y t)) (deriv (gam x y) t) =
      ∫ t in (0 : ℝ)..1, (8 : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [D_countable.ae_notMem volume] with t ht _
    obtain ⟨φ, ψ, hd, hc⟩ := gam_deriv x y ht
    rw [hd.deriv]
    have hxy := H.hxy
    simp only [gam, J, phaseInner, inner_neg_left, inner_smul_left, inner_smul_right,
      conj_trivial]
    rw [real_inner_comm x y, hxy]
    rcases hc with ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ <;>
      rw [h] <;> ring
  rw [this]; norm_num

lemma XY.nonconst (H : XY K x y) : gam x y 0 ≠ gam x y (1/2) := by
  intro h
  have h1 := congrArg Prod.fst h
  simp only [gam, F_zero, F_half, one_smul, neg_one_smul] at h1
  have hx0 : x = 0 := by
    have : (2 : ℝ) • x = 0 := by rw [two_smul]; nth_rewrite 2 [h1]; exact add_neg_cancel x
    exact (smul_eq_zero.1 this).resolve_left (by norm_num)
  have := H.hxy
  rw [hx0, inner_zero_left] at this
  norm_num at this

lemma XY.cEHZ_le (H : XY K x y) : cEHZ (K ×ˢ polar K) ≤ 4 := by
  refine (iInf₂_le (gam x y) ⟨H.gcc, 0, 1/2, H.nonconst⟩).trans ?_
  rw [H.action_eq]; norm_num

lemma exists_xy (hn : 1 ≤ n) (K : Set (Position n)) (hK : IsSymmetricConvexBody K) :
    ∃ x y : Position n, XY K x y := by
  obtain ⟨hc, hconv, hint, hsym⟩ := hK
  have hz : ∃ z ∈ K, z ≠ 0 := by
    by_contra h
    push Not at h
    have : Nontrivial (Position n) :=
      ⟨⟨EuclideanSpace.single (⟨0, hn⟩ : Fin n) 1, 0, by simp⟩⟩
    have hsub : K ⊆ {0} := fun z hz => h z hz
    have := interior_mono hsub
    rw [interior_singleton] at this
    obtain ⟨w, hw⟩ := hint
    exact this hw
  obtain ⟨z, hzK, hz0⟩ := hz
  obtain ⟨x, hxK, hmax⟩ := hc.exists_isMaxOn ⟨z, hzK⟩
    (f := fun q => inner ℝ q z) (by fun_prop)
  have hs : 0 < inner ℝ x z := lt_of_lt_of_le (real_inner_self_pos.2 hz0) (hmax hzK)
  refine ⟨x, (inner ℝ x z)⁻¹ • z, ⟨hconv, hsym, hxK, ?_, ?_⟩⟩
  · intro q hq
    rw [inner_smul_right]
    have : inner ℝ q z ≤ inner ℝ x z := hmax hq
    rw [inv_mul_le_iff₀ hs]; linarith
  · rw [inner_smul_right]; field_simp

end Loop

/-! ## Mahler on `EuclideanSpace` -/

lemma mahler_euclid {n : ℕ} (hn : 1 ≤ n) (K : Set (Position n)) (hK : IsSymmetricConvexBody K) :
    ENNReal.ofReal (4 ^ n / n.factorial) ≤ volume K * volume (polar K) := by
  obtain ⟨hc, hconv, hint, hsym⟩ := hK
  set L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  set K' : Set (Fin n → ℝ) := L.symm ⁻¹' K with hK'
  have hvol : ∀ S : Set (Position n), volume (L.symm ⁻¹' S) = volume S := fun S =>
    ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).symm).measure_preimage_equiv S
  have hpol : OAI.SymmetricMahler.coordinatePolar K' = L.symm ⁻¹' polar K := by
    ext p
    simp only [OAI.SymmetricMahler.coordinatePolar, polar, K', mem_preimage, mem_ofPred_eq]
    constructor
    · intro h q hq
      have := h (L q) (by simpa using hq)
      simpa [PiLp.inner_apply, L, mul_comm] using this
    · intro h v hv
      have := h _ hv
      simpa [PiLp.inner_apply, L, mul_comm] using this
  have himg : K' = L '' K := (L.toEquiv.image_eq_preimage_symm K).symm
  have h := OAI.SymmetricMahler.symmetric_mahler hn (K := K') ?_ ?_ ?_ ?_
  · rw [hpol, hvol, hvol, ← ENNReal.toReal_mul] at h
    exact (ENNReal.ofReal_le_ofReal h).trans ENNReal.ofReal_toReal_le
  · rw [himg]; exact hc.image L.continuous
  · exact hconv.linear_preimage L.symm.toLinearMap
  · intro v hv
    simp only [K', mem_preimage, map_neg] at hv ⊢
    exact (hsym _).1 hv
  · obtain ⟨w, hw⟩ := hint
    refine ⟨L w, ?_⟩
    have := L.symm.toHomeomorph.preimage_interior K
    change L w ∈ interior (⇑L.symm.toHomeomorph ⁻¹' K)
    rw [← this]
    simpa using hw

end Viterbo.MahlerIff

open MeasureTheory
open scoped ENNReal

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    (∀ K : Set (OAI.SymmetricPolar.Position n), OAI.SymmetricPolar.IsSymmetricConvexBody K →
        Viterbo.cEHZ (K ×ˢ OAI.SymmetricPolar.polar K) ^ n ≤
          (n.factorial : ℝ≥0∞) * volume (K ×ˢ OAI.SymmetricPolar.polar K)) ↔
      ∀ K : Set (OAI.SymmetricPolar.Position n), OAI.SymmetricPolar.IsSymmetricConvexBody K →
        ENNReal.ofReal (4 ^ n / n.factorial) ≤ volume K * volume (OAI.SymmetricPolar.polar K) := by
  have R := fun K hK => Viterbo.MahlerIff.mahler_euclid hn K hK
  refine ⟨fun _ => R, fun _ => ?_⟩
  intro K hK
  obtain ⟨x, y, H⟩ := Viterbo.MahlerIff.exists_xy hn K hK
  have hc := H.cEHZ_le
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  have h4 : (4 : ℝ≥0∞) ^ n = (n.factorial : ℝ≥0∞) * ENNReal.ofReal (4 ^ n / n.factorial) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      mul_div_cancel₀ _ (by positivity : (n.factorial : ℝ) ≠ 0), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
  calc Viterbo.cEHZ (K ×ˢ OAI.SymmetricPolar.polar K) ^ n ≤ 4 ^ n := by gcongr
    _ = (n.factorial : ℝ≥0∞) * ENNReal.ofReal (4 ^ n / n.factorial) := h4
    _ ≤ (n.factorial : ℝ≥0∞) * (volume K * volume (OAI.SymmetricPolar.polar K)) := by
      gcongr; exact R K hK
