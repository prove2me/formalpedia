-- Prove2me | solution 1 for SquarePeg.nielsen_wright_symmetric_curve
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T22:43:26.655161+00:00
-- url     : https://prove2.me/submissions/6bf2d4ce-88b4-4827-bc0c-ed86d73d7ae1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SchoenfliesCurveCore
import Definitions.Def_SquarePeg_shapes
import Definitions.Def_SquarePeg_classes
import Definitions.Def_SquarePeg_similarity
import Theorems.Thm_LefebvreVariations_zero_set_crossing_continuum

set_option autoImplicit false

open Schoenflies SquarePeg Set




/-- A periodic parametrization of a Jordan curve. -/
private structure PLoop (C : Set Plane) (g : ℝ → Plane) : Prop where
  cont : Continuous g
  per : ∀ t, g (t + 1) = g t
  mem : ∀ t, g t ∈ C
  shift : ∀ p ∈ C, ∀ τ : ℝ, ∃ t ∈ Ico τ (τ + 1), g t = p
  inj : ∀ s t, g s = g t → |s - t| < 1 → s = t

private lemma ploop_of_jordan (C : Set Plane) (hC : IsJordanCurve C) :
    ∃ g : ℝ → Plane, PLoop C g := by
  obtain ⟨f, hf, rfl⟩ := hC
  refine ⟨f ∘ Int.fract, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · exact ContinuousOn.comp_fract'' hf.continuousOn hf.closes
  · intro t; simp [Int.fract_add_one]
  · intro t
    exact ⟨Int.fract t, ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, rfl⟩
  · rintro p ⟨x, hx, rfl⟩ τ
    have key : ∃ y ∈ Ico (0 : ℝ) 1, f y = f x := by
      rcases eq_or_lt_of_le hx.2 with h | h
      · exact ⟨0, ⟨le_rfl, one_pos⟩, by rw [h]; exact hf.closes⟩
      · exact ⟨x, ⟨hx.1, h⟩, rfl⟩
    obtain ⟨y, hy, hyx⟩ := key
    refine ⟨τ + Int.fract (y - τ), ⟨by linarith [Int.fract_nonneg (y - τ)],
      by linarith [Int.fract_lt_one (y - τ)]⟩, ?_⟩
    have h1 : Int.fract (τ + Int.fract (y - τ)) = y := by
      rw [Int.fract_eq_iff]
      refine ⟨hy.1, hy.2, ⌊y - τ⌋ * (-1), ?_⟩
      rw [Int.fract]; push_cast; ring
    simp only [Function.comp, h1, hyx]
  · intro s t hst hlt
    have h1 : Int.fract s = Int.fract t :=
      hf.injOn ⟨Int.fract_nonneg s, Int.fract_lt_one s⟩
        ⟨Int.fract_nonneg t, Int.fract_lt_one t⟩ hst
    obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp h1
    rw [hz] at hlt
    have : z = 0 := by
      have h2 : |(z : ℝ)| < 1 := hlt
      rw [abs_lt] at h2
      have h3 : (-1 : ℤ) < z := by exact_mod_cast h2.1
      have h4 : z < 1 := by exact_mod_cast h2.2
      omega
    rw [this] at hz; simp at hz; linarith

/-- Unit normal. -/
private noncomputable def nrm (u : Plane) : Plane := !₂[-(u 1), u 0]

private lemma norm_sq_coord (v : Plane) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [sq_abs]

private lemma comb_norm_sq (u : Plane) (hu : u 0 ^ 2 + u 1 ^ 2 = 1) (α β : ℝ) :
    ‖α • u + β • nrm u‖ ^ 2 = α ^ 2 + β ^ 2 := by
  rw [norm_sq_coord]
  simp [nrm]
  linear_combination (α ^ 2 + β ^ 2) * hu

private lemma decomp (u : Plane) (hu : u 0 ^ 2 + u 1 ^ 2 = 1) (v : Plane) :
    v = (v 0 * u 0 + v 1 * u 1) • u + (v 1 * u 0 - v 0 * u 1) • nrm u := by
  ext i; fin_cases i <;> simp [nrm] <;> linear_combination (-(v _)) * hu

private lemma norm_eq_of_sq {v w : Plane} (h : ‖v‖ ^ 2 = ‖w‖ ^ 2) : ‖v‖ = ‖w‖ :=
  (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

private lemma line_square (a u : Plane) (hu : u 0 ^ 2 + u 1 ^ 2 = 1) (x y y' : ℝ)
    (hx : x ≠ 0) (hy : (y' - y) ^ 2 = 4 * x ^ 2) :
    IsSquare (a + y • u + x • nrm u) (a + y' • u + x • nrm u)
      (a + y' • u - x • nrm u) (a + y • u - x • nrm u) := by
  have e13 : (a + y • u + x • nrm u) - (a + y' • u - x • nrm u)
      = (y - y') • u + (2 * x) • nrm u := by module
  have e24 : (a + y' • u + x • nrm u) - (a + y • u - x • nrm u)
      = (y' - y) • u + (2 * x) • nrm u := by module
  have e12 : (a + y • u + x • nrm u) - (a + y' • u + x • nrm u)
      = (y - y') • u + (0 : ℝ) • nrm u := by module
  have e23 : (a + y' • u + x • nrm u) - (a + y' • u - x • nrm u)
      = (0 : ℝ) • u + (2 * x) • nrm u := by module
  have hx2 : 0 < x ^ 2 := by positivity
  refine ⟨⟨by module, ?_, ?_, ?_⟩, ?_⟩
  · rw [dist_eq_norm, dist_eq_norm, e13, e24]
    apply norm_eq_of_sq
    rw [comb_norm_sq u hu, comb_norm_sq u hu]; ring
  · intro h
    have := congrArg (fun v => ‖v‖ ^ 2) (sub_eq_zero.mpr h)
    simp only [e12, comb_norm_sq u hu, norm_zero] at this
    nlinarith
  · intro h
    have := congrArg (fun v => ‖v‖ ^ 2) (sub_eq_zero.mpr h)
    simp only [e23, comb_norm_sq u hu, norm_zero] at this
    nlinarith
  · rw [dist_eq_norm, dist_eq_norm, e12, e23]
    apply norm_eq_of_sq
    rw [comb_norm_sq u hu, comb_norm_sq u hu]; nlinarith

private lemma point_square (z p q : Plane) (hp : p ≠ 0) (hn : ‖p‖ = ‖q‖)
    (hi : inner ℝ p q = 0) :
    IsSquare (z + p) (z + q) (z - p) (z - q) := by
  have hp2 : 0 < ‖p‖ ^ 2 := by positivity
  refine ⟨⟨by abel, ?_, ?_, ?_⟩, ?_⟩
  · rw [dist_eq_norm, dist_eq_norm]
    have e1 : z + p - (z - p) = (2 : ℝ) • p := by module
    have e2 : z + q - (z - q) = (2 : ℝ) • q := by module
    rw [e1, e2, norm_smul, norm_smul, hn]
  · intro h
    have : p = q := by simpa using h
    rw [this, real_inner_self_eq_norm_sq] at hi
    rw [hn] at hp2; linarith
  · intro h
    have : q = -p := by
      have h' := congrArg (fun v => v - z) h; simp at h'; exact h'
    rw [this, inner_neg_right, real_inner_self_eq_norm_sq] at hi
    linarith
  · rw [dist_eq_norm, dist_eq_norm]
    have e1 : z + p - (z + q) = p - q := by abel
    have e2 : z + q - (z - p) = p + q := by abel
    rw [e1, e2]
    apply norm_eq_of_sq
    rw [norm_sub_sq_real, norm_add_sq_real, hi]; ring
private def cX (u v : Plane) : ℝ := v 1 * u 0 - v 0 * u 1
private def cY (u v : Plane) : ℝ := v 0 * u 0 + v 1 * u 1
private lemma refl_formula (a u p : Plane) (hu : u 0 ^ 2 + u 1 ^ 2 = 1) :
    a + ((2 * inner ℝ (p - a) u) • u - (p - a))
      = a + cY u (p - a) • u - cX u (p - a) • nrm u := by
  have hi : inner ℝ (p - a) u = (p - a) 0 * u 0 + (p - a) 1 * u 1 := by
    simp [PiLp.inner_apply, Fin.sum_univ_two]; ring
  rw [hi]
  ext i; fin_cases i <;> simp [cX, cY, nrm]
  · linear_combination (p 0 - a 0) * hu
  · linear_combination (p 1 - a 1) * hu

private lemma cX_comb (u : Plane) (hu : u 0 ^ 2 + u 1 ^ 2 = 1) (α β : ℝ) :
    cX u (α • u + β • nrm u) = β := by
  simp [cX, nrm]; linear_combination β * hu

private lemma cY_comb (u : Plane) (hu : u 0 ^ 2 + u 1 ^ 2 = 1) (α β : ℝ) :
    cY u (α • u + β • nrm u) = α := by
  simp [cY, nrm]; linear_combination α * hu

private lemma no_real_loop (h : ℝ → ℝ) (hc : Continuous h) (hp : ∀ t, h (t + 1) = h t)
    (hi : ∀ s t, h s = h t → |s - t| < 1 → s = t) : False := by
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (zero_le_one' ℝ))
    hc.continuousOn
  have hle : ∀ t ∈ Icc m (m + 1), h t ≤ h m := by
    intro t ht
    rcases le_or_gt t 1 with h1 | h1
    · exact hmax ⟨by linarith [hm.1, ht.1], h1⟩
    · have : h t = h (t - 1) := by rw [← hp (t - 1)]; ring_nf
      rw [this]; exact hmax ⟨by linarith, by linarith [hm.2, ht.2]⟩
  set c := h (m + 1 / 2) with hcdef
  have hc1 : c < h m := by
    refine lt_of_le_of_ne (hle _ ⟨by linarith, by linarith⟩) fun heq => ?_
    have := hi _ _ heq (by rw [abs_lt]; constructor <;> linarith)
    linarith
  obtain ⟨t1, ht1, hv1⟩ := intermediate_value_Icc' (by linarith : m ≤ m + 1 / 2)
    hc.continuousOn (show (c + h m) / 2 ∈ Icc (h (m + 1 / 2)) (h m) from
      ⟨by linarith, by linarith⟩)
  obtain ⟨t2, ht2, hv2⟩ := intermediate_value_Icc (by linarith : m + 1 / 2 ≤ m + 1)
    hc.continuousOn (show (c + h m) / 2 ∈ Icc (h (m + 1 / 2)) (h (m + 1)) from
      ⟨by linarith, by rw [hp]; linarith⟩)
  have ht1m : t1 ≠ m := by intro he; rw [he] at hv1; linarith
  have ht12 : t1 = t2 := hi _ _ (hv1.trans hv2.symm) (by
    rw [abs_lt]; constructor
    · linarith [ht1.1, ht2.2, lt_of_le_of_ne ht1.1 (Ne.symm ht1m)]
    · linarith [ht1.2, ht2.1])
  have : t1 = m + 1 / 2 := le_antisymm (ht1.2) (ht12 ▸ ht2.1)
  rw [this] at hv1; linarith

private lemma line_case (C : Set Plane) (g : ℝ → Plane) (hg : PLoop C g) (a u : Plane)
    (hu1 : ‖u‖ = 1)
    (hsym : ∀ p ∈ C, a + ((2 * inner ℝ (p - a) u) • u - (p - a)) ∈ C) :
    ∃ p1 p2 p3 p4 : Plane, p1 ∈ C ∧ p2 ∈ C ∧ p3 ∈ C ∧ p4 ∈ C ∧ IsSquare p1 p2 p3 p4 := by
  have hu : u 0 ^ 2 + u 1 ^ 2 = 1 := by rw [← norm_sq_coord, hu1]; norm_num
  set X : ℝ → ℝ := fun t => cX u (g t - a) with hXdef
  set Y : ℝ → ℝ := fun t => cY u (g t - a) with hYdef
  have hXc : Continuous X := by simp only [hXdef, cX]; have := hg.cont; fun_prop
  have hYc : Continuous Y := by simp only [hYdef, cY]; have := hg.cont; fun_prop
  have hgXY : ∀ t, g t = a + Y t • u + X t • nrm u := by
    intro t
    have := decomp u hu (g t - a)
    simp only [hXdef, hYdef, cX, cY]
    rw [add_assoc, ← this]; abel
  have hσ : ∀ t τ, ∃ t' ∈ Ico τ (τ + 1), X t' = -X t ∧ Y t' = Y t := by
    intro t τ
    have hmem := hsym _ (hg.mem t)
    rw [refl_formula a u _ hu] at hmem
    obtain ⟨t', ht', heq⟩ := hg.shift _ hmem τ
    refine ⟨t', ht', ?_, ?_⟩
    · have : g t' - a = cY u (g t - a) • u + (-cX u (g t - a)) • nrm u := by
        rw [heq]; module
      simp only [hXdef]; rw [this, cX_comb u hu]
    · have : g t' - a = cY u (g t - a) • u + (-cX u (g t - a)) • nrm u := by
        rw [heq]; module
      simp only [hYdef]; rw [this, cY_comb u hu]
  have hXper : ∀ t, X (t + 1) = X t := by intro t; simp only [hXdef, hg.per]
  -- a point strictly on the positive side
  obtain ⟨t0, ht0⟩ : ∃ t0, 0 < X t0 := by
    by_contra hneg
    push Not at hneg
    have hz : ∀ t, X t = 0 := by
      intro t
      refine le_antisymm (hneg t) ?_
      by_contra hlt; push Not at hlt
      obtain ⟨t', -, h1, -⟩ := hσ t 0
      linarith [hneg t']
    refine no_real_loop Y hYc (fun t => by simp only [hYdef, hg.per]) fun s t hst hlt => ?_
    refine hg.inj s t ?_ hlt
    rw [hgXY s, hgXY t, hz s, hz t, hst]
  obtain ⟨t'', ht''I, ht''X, -⟩ := hσ t0 (t0 - 1)
  rw [sub_add_cancel] at ht''I
  have hneg'' : X t'' < 0 := by rw [ht''X]; linarith
  have hneg1 : X (t'' + 1) < 0 := by rw [hXper]; exact hneg''
  -- left end of the positive excursion
  set Zm := Icc t'' t0 ∩ {s | X s = 0} with hZm
  have hZmc : IsClosed Zm := isClosed_Icc.inter (isClosed_eq hXc continuous_const)
  have hZmb : BddAbove Zm := bddAbove_Icc.mono inter_subset_left
  have hZmn : Zm.Nonempty := by
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc (by linarith [ht''I.2] : t'' ≤ t0)
      hXc.continuousOn (show (0 : ℝ) ∈ Icc (X t'') (X t0) from ⟨hneg''.le, ht0.le⟩)
    exact ⟨s, hs, hs0⟩
  set u0 := sSup Zm
  have hu0 : u0 ∈ Zm := hZmc.csSup_mem hZmn hZmb
  have hpos_l : ∀ s, u0 < s → s ≤ t0 → 0 < X s := by
    intro s hs1 hs2
    by_contra hle; push Not at hle
    rcases hle.lt_or_eq with hlt | heq
    · obtain ⟨s', hs', hs'0⟩ := intermediate_value_Icc hs2 hXc.continuousOn
        (show (0 : ℝ) ∈ Icc (X s) (X t0) from ⟨hlt.le, ht0.le⟩)
      have : s' ≤ u0 := le_csSup hZmb ⟨⟨by linarith [hu0.1.1, hs'.1], hs'.2⟩, hs'0⟩
      linarith [hs'.1]
    · have : s ≤ u0 := le_csSup hZmb ⟨⟨by linarith [hu0.1.1], hs2⟩, heq⟩
      linarith
  -- right end
  set Zp := Icc t0 (t'' + 1) ∩ {s | X s = 0} with hZp
  have hZpc : IsClosed Zp := isClosed_Icc.inter (isClosed_eq hXc continuous_const)
  have hZpb : BddBelow Zp := bddBelow_Icc.mono inter_subset_left
  have hZpn : Zp.Nonempty := by
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' (by linarith [ht''I.1] : t0 ≤ t'' + 1)
      hXc.continuousOn (show (0 : ℝ) ∈ Icc (X (t'' + 1)) (X t0) from ⟨hneg1.le, ht0.le⟩)
    exact ⟨s, hs, hs0⟩
  set v0 := sInf Zp
  have hv0 : v0 ∈ Zp := hZpc.csInf_mem hZpn hZpb
  have hpos_r : ∀ s, t0 ≤ s → s < v0 → 0 < X s := by
    intro s hs1 hs2
    by_contra hle; push Not at hle
    rcases hle.lt_or_eq with hlt | heq
    · obtain ⟨s', hs', hs'0⟩ := intermediate_value_Icc' hs1 hXc.continuousOn
        (show (0 : ℝ) ∈ Icc (X s) (X t0) from ⟨hlt.le, ht0.le⟩)
      have : v0 ≤ s' := csInf_le hZpb ⟨⟨hs'.1, by linarith [hv0.1.2, hs'.2]⟩, hs'0⟩
      linarith [hs'.2]
    · have : v0 ≤ s := csInf_le hZpb ⟨⟨hs1, by linarith [hv0.1.2]⟩, heq⟩
      linarith
  have hXu0 : X u0 = 0 := hu0.2
  have hXv0 : X v0 = 0 := hv0.2
  have hu0t0 : u0 < t0 := lt_of_le_of_ne hu0.1.2 (by rintro h; rw [h] at hXu0; linarith)
  have ht0v0 : t0 < v0 := lt_of_le_of_ne hv0.1.1 (by rintro h; rw [← h] at hXv0; linarith)
  have ht''u0 : t'' < u0 := lt_of_le_of_ne hu0.1.1 (by rintro h; rw [← h] at hXu0; linarith)
  have hv0t'' : v0 < t'' + 1 := lt_of_le_of_ne hv0.1.2 (by rintro h; rw [h] at hXv0; linarith)
  have hpos : ∀ s ∈ Ioo u0 v0, 0 < X s := by
    intro s hs
    rcases le_total s t0 with h | h
    · exact hpos_l s hs.1 h
    · exact hpos_r s h hs.2
  have hnn : ∀ s ∈ Icc u0 v0, 0 ≤ X s := by
    intro s hs
    rcases hs.1.lt_or_eq with h1 | h1
    · rcases hs.2.lt_or_eq with h2 | h2
      · exact (hpos s ⟨h1, h2⟩).le
      · rw [h2, hXv0]
    · rw [← h1, hXu0]
  have hYne : Y u0 ≠ Y v0 := by
    intro hYe
    have : u0 = v0 := hg.inj _ _ (by rw [hgXY u0, hgXY v0, hXu0, hXv0, hYe])
      (by rw [abs_lt]; constructor <;> linarith)
    linarith
  -- the highest point of the excursion
  obtain ⟨tm, htm, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.2 (by linarith : u0 ≤ v0)) hXc.continuousOn
  set M := X tm
  have hM : 0 < M := lt_of_lt_of_le ht0 (hmax ⟨hu0t0.le, ht0v0.le⟩)
  set T := Icc u0 v0 ∩ {s | X s = M} with hT
  have hTc : IsClosed T := isClosed_Icc.inter (isClosed_eq hXc continuous_const)
  have hTb : BddBelow T := bddBelow_Icc.mono inter_subset_left
  set ts := sInf T
  have hts : ts ∈ T := hTc.csInf_mem ⟨tm, htm, rfl⟩ hTb
  have hXts : X ts = M := hts.2
  have hu0ts : u0 < ts := lt_of_le_of_ne hts.1.1 (by rintro h; rw [← h] at hXts; linarith)
  have htsv0 : ts < v0 := lt_of_le_of_ne hts.1.2 (by rintro h; rw [h] at hXts; linarith)
  have hfirst : ∀ s ∈ Icc u0 ts, X s = M → s = ts := fun s hs hsM =>
    le_antisymm hs.2 (csInf_le hTb ⟨⟨hs.1, by linarith [hs.2]⟩, hsM⟩)
  -- the crossing lemma
  obtain ⟨W, hWsub, hW0, hWc, ⟨s1, hs1⟩, ⟨s2, hs2⟩⟩ :=
    LefebvreVariations.zero_set_crossing_continuum u0 ts ts v0 hu0ts.le htsv0.le
      (fun p => X p.2 - X p.1)
      ((hXc.comp continuous_snd).sub (hXc.comp continuous_fst)).continuousOn
      (fun t ht => by
        simp only [hXu0, sub_zero]; exact hnn t ⟨by linarith [ht.1], ht.2⟩)
      (fun t ht => by
        simp only [hXts]; have := hmax ⟨by linarith [ht.1], ht.2⟩; simp at this ⊢
        exact this)
  obtain ⟨e, he2, he⟩ : ∃ e : ℝ, e ^ 2 = 1 ∧ 0 < e * (Y v0 - Y u0) := by
    rcases lt_or_gt_of_ne hYne with h | h
    · exact ⟨1, by norm_num, by linarith⟩
    · exact ⟨-1, by norm_num, by linarith⟩
  set G : ℝ × ℝ → ℝ := fun p => e * (Y p.2 - Y p.1) - 2 * X p.1 with hGdef
  have hGc : Continuous G := by simp only [hGdef]; fun_prop
  have hs1' : s1 = ts := by
    have h1 := (hWsub hs1).1
    have h0 := hW0 _ hs1
    simp only at h0
    exact hfirst s1 h1 (by linarith)
  have hzero_left : ∀ s ∈ Icc u0 ts, X s = 0 → s = u0 := by
    intro s hs hs0
    by_contra hne
    have := hpos s ⟨lt_of_le_of_ne hs.1 (Ne.symm hne), by linarith [hs.2]⟩
    linarith
  have hs2' : s2 = u0 := by
    have h1 := (hWsub hs2).1
    have h0 := hW0 _ hs2
    simp only [hXv0] at h0
    exact hzero_left s2 h1 (by linarith)
  have hG1 : G (s1, ts) < 0 := by
    simp only [hGdef, hs1', sub_self, mul_zero, zero_sub, hXts]; linarith
  have hG2 : 0 < G (s2, v0) := by
    simp only [hGdef, hs2', hXu0, mul_zero, sub_zero]; exact he
  obtain ⟨w, hw, hGw⟩ := hWc.intermediate_value hs1 hs2 hGc.continuousOn
    (show (0 : ℝ) ∈ Icc (G (s1, ts)) (G (s2, v0)) from ⟨hG1.le, hG2.le⟩)
  obtain ⟨s, t⟩ := w
  have hst := hWsub hw
  have hXst : X t = X s := by have := hW0 _ hw; simp only at this; linarith
  have hGst : e * (Y t - Y s) = 2 * X s := by simp only [hGdef] at hGw; linarith
  have hXs : X s ≠ 0 := by
    intro hXs0
    have hsu : s = u0 := hzero_left s hst.1 hXs0
    have htv : t = v0 := by
      by_contra hne
      have := hpos t ⟨by linarith [hst.2.1], lt_of_le_of_ne hst.2.2 hne⟩
      linarith
    rw [hsu, htv, hXu0] at hGst
    linarith
  have hy : (Y t - Y s) ^ 2 = 4 * X s ^ 2 := by
    have : (e * (Y t - Y s)) ^ 2 = (2 * X s) ^ 2 := by rw [hGst]
    rw [mul_pow, he2] at this; linarith
  have hσt : a + Y t • u - X s • nrm u ∈ C := by
    have := hsym _ (hg.mem t)
    rw [refl_formula a u _ hu] at this
    have e1 : cX u (g t - a) = X s := hXst
    rw [e1] at this; exact this
  have hσs : a + Y s • u - X s • nrm u ∈ C := by
    have := hsym _ (hg.mem s)
    rw [refl_formula a u _ hu] at this
    exact this
  refine ⟨_, _, _, _, ?_, ?_, hσt, hσs, line_square a u hu (X s) (Y s) (Y t) hXs hy⟩
  · rw [← hgXY s]; exact hg.mem s
  · rw [← hXst, ← hgXY t]; exact hg.mem t

private lemma point_case (C : Set Plane) (g : ℝ → Plane) (hg : PLoop C g) (z : Plane)
    (hsym : ∀ p ∈ C, 2 • z - p ∈ C) :
    ∃ p1 p2 p3 p4 : Plane, p1 ∈ C ∧ p2 ∈ C ∧ p3 ∈ C ∧ p4 ∈ C ∧ IsSquare p1 p2 p3 p4 := by
  set δ : ℝ → Plane := fun t => g t - z with hδdef
  have hδc : Continuous δ := by simp only [hδdef]; have := hg.cont; fun_prop
  have hanti : ∀ t τ, ∃ t' ∈ Ico τ (τ + 1), δ t' = -δ t := by
    intro t τ
    obtain ⟨t', ht', heq⟩ := hg.shift _ (hsym _ (hg.mem t)) τ
    refine ⟨t', ht', ?_⟩
    simp only [hδdef, heq, two_nsmul]; abel
  have hδinj : ∀ s t, δ s = δ t → |s - t| < 1 → s = t := fun s t h hl =>
    hg.inj s t (by simpa [hδdef] using h) hl
  have hδper : ∀ t, δ (t + 1) = δ t := fun t => by simp only [hδdef, hg.per]
  have hmemP : ∀ t, z + δ t ∈ C := fun t => by simpa [hδdef] using hg.mem t
  have hmemM : ∀ t, z - δ t ∈ C := fun t => by
    have := hsym _ (hg.mem t)
    have e : 2 • z - g t = z - δ t := by simp only [hδdef, two_nsmul]; abel
    rwa [e] at this
  -- the centre is not on the curve
  have hδne : ∀ t, δ t ≠ 0 := by
    intro τ hτ
    have hτ1 : δ (τ + 1) = 0 := by rw [hδper]; exact hτ
    have hin : ∀ t ∈ Icc τ (τ + 1), δ t ≠ 0 → t ∈ Ioo τ (τ + 1) := by
      intro t ht hne
      refine ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩
      · rintro rfl; exact hne hτ
      · rintro rfl; exact hne hτ1
    have hne : ∀ s ∈ Ioo τ (τ + 1), δ s ≠ 0 := by
      intro s hs h0
      have := hδinj s τ (by rw [h0, hτ]) (by rw [abs_lt]; constructor <;> linarith [hs.1, hs.2])
      linarith [hs.1]
    have hinj' : ∀ s ∈ Ioo τ (τ + 1), ∀ t ∈ Ioo τ (τ + 1), δ s = δ t → s = t :=
      fun s hs t ht h => hδinj s t h (by rw [abs_lt]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2])
    set Q := Icc τ (τ + 1) ×ˢ Icc τ (τ + 1) with hQ
    have hQc : IsCompact Q := isCompact_Icc.prod isCompact_Icc
    have hS : IsClosed {p : ℝ × ℝ | δ p.2 + δ p.1 = 0} :=
      isClosed_eq (by fun_prop) continuous_const
    set K1 := Q ∩ ({p : ℝ × ℝ | p.2 ≤ p.1} ∩ {p : ℝ × ℝ | δ p.2 + δ p.1 = 0})
    set K2 := Q ∩ ({p : ℝ × ℝ | p.1 ≤ p.2} ∩ {p : ℝ × ℝ | δ p.2 + δ p.1 = 0})
    have hK1 : IsCompact K1 :=
      hQc.inter_right ((isClosed_le continuous_snd continuous_fst).inter hS)
    have hK2 : IsCompact K2 :=
      hQc.inter_right ((isClosed_le continuous_fst continuous_snd).inter hS)
    have hD := (hK1.image continuous_fst).isClosed
    have hE := (hK2.image continuous_fst).isClosed
    have hcover : Ioo τ (τ + 1) ⊆ Prod.fst '' K1 ∪ Prod.fst '' K2 := by
      intro s hs
      obtain ⟨t, ht, hts⟩ := hanti s τ
      have hsum : δ t + δ s = 0 := by rw [hts]; abel
      have hQst : (s, t) ∈ Q := ⟨Ioo_subset_Icc_self hs, Ico_subset_Icc_self ht⟩
      rcases le_total t s with h | h
      · exact Or.inl ⟨(s, t), ⟨hQst, h, hsum⟩, rfl⟩
      · exact Or.inr ⟨(s, t), ⟨hQst, h, hsum⟩, rfl⟩
    have hdisj : Ioo τ (τ + 1) ∩ (Prod.fst '' K1 ∩ Prod.fst '' K2) = ∅ := by
      ext s
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      rintro hs ⟨⟨s', t1⟩, ⟨⟨-, ht1⟩, hle1, hsum1⟩, hs'⟩ ⟨⟨s'', t2⟩, ⟨⟨-, ht2⟩, hle2, hsum2⟩, hs''⟩
      simp only [mem_ofPred_eq] at hs' hs'' hle1 hle2 hsum1 hsum2 ht1 ht2
      rw [hs'] at hle1 hsum1; rw [hs''] at hle2 hsum2
      have hsn := hne s hs
      have e1 : δ t1 = -δ s := eq_neg_of_add_eq_zero_left hsum1
      have e2 : δ t2 = -δ s := eq_neg_of_add_eq_zero_left hsum2
      have hn1 : δ t1 ≠ 0 := by rw [e1]; exact neg_ne_zero.mpr hsn
      have hn2 : δ t2 ≠ 0 := by rw [e2]; exact neg_ne_zero.mpr hsn
      have h12 := hinj' t1 (hin t1 ht1 hn1) t2 (hin t2 ht2 hn2) (e1.trans e2.symm)
      have hst : t1 = s := le_antisymm hle1 (h12 ▸ hle2)
      rw [hst] at e1
      exact hsn (by
        have : (2 : ℝ) • δ s = 0 := by rw [two_smul]; nth_rewrite 1 [e1]; abel
        exact (smul_eq_zero.mp this).resolve_left two_ne_zero)
    have hmid : τ + 1 / 2 ∈ Ioo τ (τ + 1) := ⟨by linarith, by linarith⟩
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp isPreconnected_Ioo) _ _ hD hE
      hcover hdisj with hsub | hsub
    · obtain ⟨⟨s', t⟩, ⟨⟨-, ht⟩, hle, hsum⟩, hs'⟩ := hsub hmid
      simp only [mem_ofPred_eq] at hs' hle hsum ht; subst hs'
      have hsn := hne _ hmid
      have e1 : δ t = -δ (τ + 1 / 2) := eq_neg_of_add_eq_zero_left hsum
      have htn : δ t ≠ 0 := by rw [e1]; exact neg_ne_zero.mpr hsn
      have htI := hin t ht htn
      have hts : t < τ + 1 / 2 := lt_of_le_of_ne hle (by
        intro h; rw [h] at e1; apply hsn
        have : (2 : ℝ) • δ (τ + 1 / 2) = 0 := by rw [two_smul]; nth_rewrite 1 [e1]; abel
        exact (smul_eq_zero.mp this).resolve_left two_ne_zero)
      obtain ⟨⟨t'', t'⟩, ⟨⟨-, ht'⟩, hle', hsum'⟩, ht''⟩ := hsub htI
      simp only [mem_ofPred_eq] at ht'' hle' hsum' ht'; subst ht''
      have e2 : δ t' = δ (τ + 1 / 2) := by
        rw [eq_neg_of_add_eq_zero_left hsum', e1, neg_neg]
      have := hinj' t' (hin t' ht' (by rw [e2]; exact hsn)) _ hmid e2
      linarith
    · obtain ⟨⟨s', t⟩, ⟨⟨-, ht⟩, hle, hsum⟩, hs'⟩ := hsub hmid
      simp only [mem_ofPred_eq] at hs' hle hsum ht; subst hs'
      have hsn := hne _ hmid
      have e1 : δ t = -δ (τ + 1 / 2) := eq_neg_of_add_eq_zero_left hsum
      have htn : δ t ≠ 0 := by rw [e1]; exact neg_ne_zero.mpr hsn
      have htI := hin t ht htn
      have hts : τ + 1 / 2 < t := lt_of_le_of_ne hle (by
        rintro h; rw [← h] at e1; apply hsn
        have : (2 : ℝ) • δ (τ + 1 / 2) = 0 := by rw [two_smul]; nth_rewrite 1 [e1]; abel
        exact (smul_eq_zero.mp this).resolve_left two_ne_zero)
      obtain ⟨⟨t'', t'⟩, ⟨⟨-, ht'⟩, hle', hsum'⟩, ht''⟩ := hsub htI
      simp only [mem_ofPred_eq] at ht'' hle' hsum' ht'; subst ht''
      have e2 : δ t' = δ (τ + 1 / 2) := by
        rw [eq_neg_of_add_eq_zero_left hsum', e1, neg_neg]
      have := hinj' t' (hin t' ht' (by rw [e2]; exact hsn)) _ hmid e2
      linarith
  -- extreme distances to the centre
  set N : ℝ → ℝ := fun t => ‖δ t‖ with hNdef
  have hNc : Continuous N := by simp only [hNdef]; fun_prop
  obtain ⟨s0, -, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.2 (zero_le_one' ℝ)) hNc.continuousOn
  obtain ⟨s1, -, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.2 (zero_le_one' ℝ)) hNc.continuousOn
  have hglob : ∀ t, N s0 ≤ N t ∧ N t ≤ N s1 := by
    intro t
    obtain ⟨t', ht', heq⟩ := hg.shift _ (hg.mem t) 0
    have : N t = N t' := by simp only [hNdef, hδdef, heq]
    rw [this]
    exact ⟨hmin (Ico_subset_Icc_self (by simpa using ht')),
      hmax (Ico_subset_Icc_self (by simpa using ht'))⟩
  have hr : 0 < N s0 := norm_pos_iff.mpr (hδne s0)
  have sqr : ∀ s t, ‖δ s‖ = ‖δ t‖ → inner ℝ (δ s) (δ t) = 0 →
      ∃ p1 p2 p3 p4 : Plane, p1 ∈ C ∧ p2 ∈ C ∧ p3 ∈ C ∧ p4 ∈ C ∧ IsSquare p1 p2 p3 p4 :=
    fun s t hn hi => ⟨_, _, _, _, hmemP s, hmemP t, hmemM s, hmemM t,
      point_square z (δ s) (δ t) (hδne s) hn hi⟩
  rcases (hglob s1).1.lt_or_eq with hlt | heq
  swap
  · -- all points at the same distance: one intermediate value argument
    obtain ⟨t1, ht1, hanti1⟩ := hanti s0 s0
    have hφ : Continuous fun t => inner ℝ (δ s0) (δ t) := by fun_prop
    have hpos : 0 < ‖δ s0‖ ^ 2 := by positivity
    obtain ⟨t, -, ht⟩ := intermediate_value_Icc' ht1.1 hφ.continuousOn
      (show (0 : ℝ) ∈ Icc (inner ℝ (δ s0) (δ t1)) (inner ℝ (δ s0) (δ s0)) from by
        rw [hanti1, inner_neg_right, real_inner_self_eq_norm_sq]; constructor <;> linarith)
    refine sqr s0 t ?_ ht
    have := hglob t
    exact le_antisymm this.1 (le_of_le_of_eq this.2 heq.symm)
  · obtain ⟨s1', hs1'I, hs1'⟩ := hg.shift _ (hg.mem s1) s0
    have hN1 : N s1' = N s1 := by simp only [hNdef, hδdef, hs1']
    set A := Icc s0 s1' ∩ {s | N s = N s0} with hA
    have hAc : IsClosed A := isClosed_Icc.inter (isClosed_eq hNc continuous_const)
    have hAb : BddAbove A := bddAbove_Icc.mono inter_subset_left
    set σ0 := sSup A
    have hσ0 : σ0 ∈ A := hAc.csSup_mem ⟨s0, ⟨le_rfl, hs1'I.1⟩, rfl⟩ hAb
    set B := Icc σ0 s1' ∩ {s | N s = N s1} with hB
    have hBc : IsClosed B := isClosed_Icc.inter (isClosed_eq hNc continuous_const)
    have hBb : BddBelow B := bddBelow_Icc.mono inter_subset_left
    set σ1 := sInf B
    have hσ1 : σ1 ∈ B := hBc.csInf_mem ⟨s1', ⟨hσ0.1.2, le_rfl⟩, hN1⟩ hBb
    have hNσ0 : N σ0 = N s0 := hσ0.2
    have hNσ1 : N σ1 = N s1 := hσ1.2
    have hσ01 : σ0 < σ1 := lt_of_le_of_ne hσ1.1.1 (by
      intro h; rw [h, hNσ1] at hNσ0; linarith)
    have hAonly : ∀ s ∈ Icc σ0 σ1, N s = N s0 → s = σ0 := fun s hs hNs =>
      le_antisymm (le_csSup hAb ⟨⟨by linarith [hσ0.1.1, hs.1], by linarith [hσ1.1.2, hs.2]⟩,
        hNs⟩) hs.1
    have hBonly : ∀ s ∈ Icc σ0 σ1, N s = N s1 → s = σ1 := fun s hs hNs =>
      le_antisymm hs.2 (csInf_le hBb ⟨⟨hs.1, by linarith [hσ1.1.2, hs.2]⟩, hNs⟩)
    obtain ⟨t1, ht1, hanti1⟩ := hanti σ1 σ0
    have hNt1 : N t1 = N s1 := by simp only [hNdef] at hNσ1 ⊢; rw [hanti1, norm_neg]; exact hNσ1
    obtain ⟨W, hWsub, hW0, hWc, ⟨w1, hw1⟩, ⟨w2, hw2⟩⟩ :=
      LefebvreVariations.zero_set_crossing_continuum σ0 σ1 σ0 t1 hσ01.le ht1.1
        (fun p => N p.2 - N p.1)
        ((hNc.comp continuous_snd).sub (hNc.comp continuous_fst)).continuousOn
        (fun t _ => by simp only [hNσ0]; linarith [(hglob t).1])
        (fun t _ => by simp only [hNσ1]; linarith [(hglob t).2])
    set G : ℝ × ℝ → ℝ := fun p => inner ℝ (δ p.1) (δ p.2) with hGdef
    have hGc : Continuous G := by simp only [hGdef]; fun_prop
    have hw1' : w1 = σ0 := by
      have h0 := hW0 _ hw1; simp only at h0
      exact hAonly w1 (hWsub hw1).1 (by linarith)
    have hw2' : w2 = σ1 := by
      have h0 := hW0 _ hw2; simp only at h0
      exact hBonly w2 (hWsub hw2).1 (by linarith)
    have hG1 : 0 < G (w1, σ0) := by
      simp only [hGdef, hw1', real_inner_self_eq_norm_sq]
      have : 0 < ‖δ σ0‖ := norm_pos_iff.mpr (hδne σ0)
      positivity
    have hG2 : G (w2, t1) < 0 := by
      simp only [hGdef, hw2', hanti1, inner_neg_right, real_inner_self_eq_norm_sq]
      have : 0 < ‖δ σ1‖ := norm_pos_iff.mpr (hδne σ1)
      nlinarith
    obtain ⟨⟨s, t⟩, hw, hGw⟩ := hWc.intermediate_value hw2 hw1 hGc.continuousOn
      (show (0 : ℝ) ∈ Icc (G (w2, t1)) (G (w1, σ0)) from ⟨hG2.le, hG1.le⟩)
    have h0 := hW0 _ hw; simp only at h0
    exact sqr s t (by simp only [hNdef] at h0; linarith) hGw

theorem solution (C : Set Plane) (hC : IsJordanCurve C)
    (hsym : IsLineSymmetric C ∨ IsPointSymmetric C) :
    ∃ p1 p2 p3 p4 : Plane, p1 ∈ C ∧ p2 ∈ C ∧ p3 ∈ C ∧ p4 ∈ C ∧ IsSquare p1 p2 p3 p4 := by
  obtain ⟨g, hg⟩ := ploop_of_jordan C hC
  rcases hsym with ⟨a, u, hu, h⟩ | ⟨z, h⟩
  · exact line_case C g hg a u hu h
  · exact point_case C g hg z h
