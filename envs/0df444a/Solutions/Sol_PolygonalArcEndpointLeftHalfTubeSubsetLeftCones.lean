-- Prove2me | solution 1 for PolygonalArcEndpointLeftHalfTubeSubsetLeftCones
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:35:51.824571+00:00
-- url     : https://prove2.me/submissions/840e1b7f-ae97-4257-8e3e-56ae9354ad28

import Mathlib
import Definitions.Def_PolygonalArc
import Definitions.Def_PolygonalArcCollarCompatibleOrientedTubeData
import Definitions.Def_PolygonalArcCollarControlRadii
import Definitions.Def_PolygonalArcCollarMiddleForbiddenMargins
import Definitions.Def_PolygonalArcCollarMiddleSegmentData
import Definitions.Def_PolygonalArcEndpointIsolation
import Definitions.Def_PolygonalArcInitialEndpointLeftCone
import Definitions.Def_PolygonalArcReverse
import Definitions.Def_PolygonalArcTerminalEndpointLeftCone

set_option autoImplicit false

lemma P7a_sq_lt (p0 p1 : EuclideanSpace ℝ (Fin 2)) (u w r : ℝ) (hne : p0 ≠ p1)
    (hd : dist (p0 + u • (p1 - p0) + w • PlanarRot90 (p1 - p0)) p0 < r) :
    u ^ 2 + w ^ 2 < (r / dist p0 p1) ^ 2 := by
  have hD : 0 < dist p0 p1 := dist_pos.mpr hne
  have h1 : dist (p0 + u • (p1 - p0) + w • PlanarRot90 (p1 - p0)) p0 ^ 2
      = (u ^ 2 + w ^ 2) * dist p0 p1 ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq]
    simp [Fin.sum_univ_two, Real.dist_eq, sq_abs, PlanarRot90]
    ring
  rw [div_pow, lt_div_iff₀ (by positivity), ← h1]
  exact pow_lt_pow_left₀ hd dist_nonneg (by norm_num)

lemma P7a_chart (p0 p1 z : EuclideanSpace ℝ (Fin 2)) (r u w : ℝ) (P : ℝ → ℝ → Prop)
    (hne : p0 ≠ p1)
    (hz : z = p0 + u • (p1 - p0) + w • PlanarRot90 (p1 - p0)) (hd : dist z p0 < r)
    (hP : P u w) :
    z ∈ (fun y : EuclideanSpace ℝ (Fin 2) => p0 + y 0 • (p1 - p0) + y 1 • PlanarRot90 (p1 - p0)) ''
      {y | P (y 0) (y 1) ∧ y 0 ^ 2 + y 1 ^ 2 < (r / dist p0 p1) ^ 2} := by
  subst hz
  refine ⟨WithLp.toLp 2 ![u, w], ?_, ?_⟩
  · have h0 : (WithLp.toLp 2 ![u, w] : EuclideanSpace ℝ (Fin 2)) 0 = u := rfl
    have h1 : (WithLp.toLp 2 ![u, w] : EuclideanSpace ℝ (Fin 2)) 1 = w := rfl
    simp only [Set.mem_setOf_eq, h0, h1]
    exact ⟨hP, P7a_sq_lt p0 p1 u w r hne hd⟩
  · rfl

lemma P7a_fwd (a b : EuclideanSpace ℝ (Fin 2)) (t s : ℝ) :
    AffineMap.lineMap a b t + s • PlanarRot90 (b - a)
      = a + t • (b - a) + s • PlanarRot90 (b - a) := by
  rw [AffineMap.lineMap_apply_module']
  abel

lemma P7a_rev (a b : EuclideanSpace ℝ (Fin 2)) (t s : ℝ) :
    AffineMap.lineMap a b t + s • PlanarRot90 (b - a)
      = b + (1 - t) • (a - b) + (-s) • PlanarRot90 (a - b) := by
  ext i
  fin_cases i <;> simp [PlanarRot90, AffineMap.lineMap_apply_module'] <;> ring

open Classical in
theorem solution (γ : PolygonalArc)
    {η : ℝ} (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (compatibleTubes :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (r₀ r₁ K₀ K₁ : ℝ) :
    PolygonalArcEndpointIsolation γ r₀ r₁ →
      0 < K₀ →
        0 < K₁ →
          ∀ (hfirst : 0 + 1 < γ.vertices.length)
            (hlast : (γ.vertices.length - 2) + 1 < γ.vertices.length),
            compatibleTubes.initialConeBound 0 hfirst < K₀ →
              compatibleTubes.terminalConeBound (γ.vertices.length - 2) hlast <
                K₁ →
                (compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf
                    0 hfirst ∩ Metric.ball γ.source r₀ ⊆
                  PolygonalArcInitialEndpointLeftCone γ r₀ K₀) ∧
                  (compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf
                      (γ.vertices.length - 2) hlast ∩
                        Metric.ball γ.target r₁ ⊆
                    PolygonalArcTerminalEndpointLeftCone γ r₁ K₁) ∧
                    (compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf
                        0 hfirst ∩ Metric.ball γ.source r₀ ⊆
                      PolygonalArcTerminalEndpointLeftCone
                        (PolygonalArcReverse γ) r₀ K₀) ∧
                      (compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf
                          (γ.vertices.length - 2) hlast ∩
                            Metric.ball γ.target r₁ ⊆
                        PolygonalArcInitialEndpointLeftCone
                          (PolygonalArcReverse γ) r₁ K₁) := by
  intro _hiso hK₀ hK₁ hfirst hlast hB₀ hB₁
  set T := compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData with hT
  have hnormal : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      T.normal j hj = PlanarRot90 (γ.vertices[j + 1] - γ.vertices[j]) := by
    intro j hj
    rw [hT, compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn]
    rfl
  have hne : ∀ (j : ℕ) (hj : j + 1 < γ.vertices.length),
      γ.vertices[j] ≠ γ.vertices[j + 1] := by
    intro j hj h
    have := (γ.simple_vertices.getElem_inj_iff).mp h
    omega
  have hsrc : γ.vertices[0]'(by omega) = γ.source := by
    have h := γ.source_eq_head
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  have htgt : γ.vertices[(γ.vertices.length - 2) + 1]'hlast = γ.target := by
    have h := γ.target_eq_last
    rw [List.getLast?_eq_getElem?,
      show γ.vertices.length - 1 = (γ.vertices.length - 2) + 1 by omega,
      List.getElem?_eq_getElem hlast] at h
    exact Option.some.inj h
  have hB₀pos := compatibleTubes.initialConeBound_pos 0 hfirst
  have hB₁pos := compatibleTubes.terminalConeBound_pos (γ.vertices.length - 2) hlast
  have hw₀ := compatibleTubes.initial_halfWidth_lt_cone_mul_lowerParam 0 hfirst
  have hw₁ := compatibleTubes.terminal_halfWidth_lt_cone_mul_one_sub_upperParam
    (γ.vertices.length - 2) hlast
  have hlow₀ := T.lowerParam_pos 0 hfirst
  have hup₁ := T.upperParam_lt_one (γ.vertices.length - 2) hlast
  have hrevV1 : ∀ h, (PolygonalArcReverse γ).vertices[1]'h
      = γ.vertices[γ.vertices.length - 2]'(by omega) := by
    intro h
    have hv : (PolygonalArcReverse γ).vertices = γ.vertices.reverse := rfl
    simp only [hv, List.getElem_reverse, List.length_reverse]
    congr 1
  have hrevVl : ∀ h, (PolygonalArcReverse γ).vertices[(PolygonalArcReverse γ).vertices.length - 2]'h
      = γ.vertices[1]'hfirst := by
    intro h
    have hv : (PolygonalArcReverse γ).vertices = γ.vertices.reverse := rfl
    simp only [hv, List.getElem_reverse, List.length_reverse]
    congr 1
    have := γ.length_ge_two
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro z ⟨hzL, hzB⟩
    rw [T.leftHalf_eq] at hzL
    obtain ⟨t, ⟨ht1, ht2⟩, s, ⟨hs1, hs2⟩, rfl⟩ := hzL
    rw [Metric.mem_ball] at hzB
    have hst : s < K₀ * t := by
      have : compatibleTubes.initialConeBound 0 hfirst * T.lowerParam 0 hfirst
          < compatibleTubes.initialConeBound 0 hfirst * t :=
        mul_lt_mul_of_pos_left ht1 hB₀pos
      have : compatibleTubes.initialConeBound 0 hfirst * t < K₀ * t :=
        mul_lt_mul_of_pos_right hB₀ (by linarith)
      linarith
    have key := P7a_chart γ.source (γ.vertices[1]'hfirst) _ r₀ t s
      (fun a b => 0 < a ∧ 0 < b ∧ b < K₀ * a) (by rw [← hsrc]; exact hne 0 hfirst)
      (by rw [hnormal, P7a_fwd, ← hsrc]) hzB (show 0 < t ∧ 0 < s ∧ s < K₀ * t from ⟨by linarith, hs1, hst⟩)
    refine Set.image_mono ?_ key
    intro y hy
    exact ⟨hy.1.1, hy.2, hy.1.2.1, hy.1.2.2⟩
  · rintro z ⟨hzL, hzB⟩
    rw [T.leftHalf_eq] at hzL
    obtain ⟨t, ⟨ht1, ht2⟩, s, ⟨hs1, hs2⟩, rfl⟩ := hzL
    rw [Metric.mem_ball] at hzB
    have hst : s < K₁ * (1 - t) := by
      have : compatibleTubes.terminalConeBound _ hlast * (1 - T.upperParam _ hlast)
          < compatibleTubes.terminalConeBound _ hlast * (1 - t) :=
        mul_lt_mul_of_pos_left (by linarith) hB₁pos
      have : compatibleTubes.terminalConeBound _ hlast * (1 - t) < K₁ * (1 - t) :=
        mul_lt_mul_of_pos_right hB₁ (by linarith)
      linarith
    have key := P7a_chart γ.target (γ.vertices[γ.vertices.length - 2]'(by omega)) _ r₁
      (1 - t) (-s)
      (fun a b => 0 < a ∧ -K₁ * a < b ∧ b < 0)
      (by rw [← htgt]; exact (hne _ hlast).symm)
      (by rw [hnormal, P7a_rev, ← htgt]) hzB (show 0 < 1 - t ∧ -K₁ * (1 - t) < -s ∧ -s < 0 from ⟨by linarith, by linarith, by linarith⟩)
    refine Set.image_mono ?_ key
    intro y hy
    exact ⟨hy.1.1, hy.2, hy.1.2.1, hy.1.2.2⟩
  · rintro z ⟨hzL, hzB⟩
    rw [T.rightHalf_eq] at hzL
    obtain ⟨t, ⟨ht1, ht2⟩, s, ⟨hs1, hs2⟩, rfl⟩ := hzL
    rw [Metric.mem_ball] at hzB
    have hst : -K₀ * t < s := by
      have : compatibleTubes.initialConeBound 0 hfirst * T.lowerParam 0 hfirst
          < compatibleTubes.initialConeBound 0 hfirst * t :=
        mul_lt_mul_of_pos_left ht1 hB₀pos
      have : compatibleTubes.initialConeBound 0 hfirst * t < K₀ * t :=
        mul_lt_mul_of_pos_right hB₀ (by linarith)
      linarith
    have key := P7a_chart γ.source (γ.vertices[1]'hfirst) _ r₀ t s
      (fun a b => 0 < a ∧ -K₀ * a < b ∧ b < 0) (by rw [← hsrc]; exact hne 0 hfirst)
      (by rw [hnormal, P7a_fwd, ← hsrc]) hzB (show 0 < t ∧ -K₀ * t < s ∧ s < 0 from ⟨by linarith, hst, hs2⟩)
    unfold PolygonalArcTerminalEndpointLeftCone
    simp only [hrevVl]
    refine Set.image_mono ?_ key
    intro y hy
    exact ⟨hy.1.1, hy.2, hy.1.2.1, hy.1.2.2⟩
  · rintro z ⟨hzL, hzB⟩
    rw [T.rightHalf_eq] at hzL
    obtain ⟨t, ⟨ht1, ht2⟩, s, ⟨hs1, hs2⟩, rfl⟩ := hzL
    rw [Metric.mem_ball] at hzB
    have hst : -s < K₁ * (1 - t) := by
      have : compatibleTubes.terminalConeBound _ hlast * (1 - T.upperParam _ hlast)
          < compatibleTubes.terminalConeBound _ hlast * (1 - t) :=
        mul_lt_mul_of_pos_left (by linarith) hB₁pos
      have : compatibleTubes.terminalConeBound _ hlast * (1 - t) < K₁ * (1 - t) :=
        mul_lt_mul_of_pos_right hB₁ (by linarith)
      linarith
    have key := P7a_chart γ.target (γ.vertices[γ.vertices.length - 2]'(by omega)) _ r₁
      (1 - t) (-s)
      (fun a b => 0 < a ∧ 0 < b ∧ b < K₁ * a)
      (by rw [← htgt]; exact (hne _ hlast).symm)
      (by rw [hnormal, P7a_rev, ← htgt]) hzB (show 0 < 1 - t ∧ 0 < -s ∧ -s < K₁ * (1 - t) from ⟨by linarith, by linarith, hst⟩)
    unfold PolygonalArcInitialEndpointLeftCone
    simp only [hrevV1]
    refine Set.image_mono ?_ key
    intro y hy
    exact ⟨hy.1.1, hy.2, hy.1.2.1, hy.1.2.2⟩
