-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P26.centralQuadratic_recession
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T21:47:42.385467+00:00
-- url     : https://prove2.me/submissions/935506f1-38a7-4c92-bcdb-3e4a0290c74c

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P26

namespace QAlgorithms.Papers.Independent.Frontier30.P26

noncomputable section

open Set Filter Topology

open QAlgorithms.Papers.Independent.Dependency50.P12.Coordinates (expAd)

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] QAlgorithms.Papers.Independent.Frontier30.P26.lieNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Frontier30.P26.lieNormedSpace

namespace X7Z10C

variable {G : Type*} [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G]

theorem X7_exp3 (N : G →L[ℝ] G) (x : G) (h3 : N (N (N x)) = 0) :
    NormedSpace.exp N x = x + N x + (1 / 2 : ℝ) • N (N x) := by
  haveI : CompleteSpace G := FiniteDimensional.complete ℝ G
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) N
  have hx := hs.mapL (ContinuousLinearMap.apply ℝ G x)
  simp only [ContinuousLinearMap.apply_apply] at hx
  have hfin : HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹) • N ^ n) x)
      (∑ n ∈ Finset.range 3, (((n.factorial : ℝ)⁻¹) • N ^ n) x) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [ContinuousLinearMap.smul_apply, show 3 + m = m + 3 by ring, pow_add, ContinuousLinearMap.mul_apply]
    have : (N ^ 3) x = 0 := by
      simp only [pow_succ, pow_zero, one_mul, ContinuousLinearMap.mul_apply]
      exact h3
    rw [this, map_zero, smul_zero]
  rw [hx.unique hfin]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    ContinuousLinearMap.smul_apply, pow_zero, pow_one, pow_two,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply]
  norm_num

theorem X7_rec_closed (K : Set G) (hK : IsClosed K) : IsClosed (recession K) := by
  have : recession K = ⋂ y ∈ K, (fun v => y + v) ⁻¹' K := by
    ext v
    simp [recession]
  rw [this]
  exact isClosed_biInter (fun y _ => hK.preimage (continuous_const.add continuous_id))

theorem X7_rec_convex (K : Set G) (hK : Convex ℝ K) : Convex ℝ (recession K) := by
  intro u hu w hw a b ha hb hab y hy
  have h1 := hu y hy
  have h2 := hw y hy
  have : y + (a • u + b • w) = a • (y + u) + b • (y + w) := by
    rw [smul_add, smul_add]
    have : y = a • y + b • y := by rw [← add_smul, hab, one_smul]
    conv_lhs => rw [this]
    abel
  rw [this]
  exact hK h1 h2 ha hb hab

theorem X7_rec_nsmul (K : Set G) (u : G) (hu : u ∈ recession K) (n : ℕ) :
    (n : ℝ) • u ∈ recession K := by
  induction n with
  | zero => intro y hy; simpa using hy
  | succ n ih =>
    intro y hy
    have := hu _ (ih y hy)
    rw [Nat.cast_succ, add_smul, one_smul, ← add_assoc]
    exact this

theorem X7_rec_smul (K : Set G) (hK : Convex ℝ K) (u : G) (hu : u ∈ recession K)
    (t : ℝ) (ht : 0 ≤ t) : t • u ∈ recession K := by
  rcases ht.eq_or_lt with h0 | hpos
  · rw [← h0, zero_smul]; intro y hy; simpa using hy
  obtain ⟨n, hn⟩ := exists_nat_ge t
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le hpos hn
  intro y hy
  have h1 := X7_rec_nsmul K u hu n y hy
  have hc : y + t • u = (1 - t / n) • y + (t / n) • (y + (n : ℝ) • u) := by
    rw [smul_add, smul_smul, div_mul_cancel₀ t hnpos.ne', sub_smul, one_smul]
    abel
  rw [hc]
  have hle : t / n ≤ 1 := (div_le_one hnpos).mpr hn
  exact hK hy h1 (by linarith) (div_nonneg hpos.le hnpos.le) (by ring)

theorem X7_center_bracket {z : G} (hz : z ∈ LieAlgebra.center ℝ G) (y : G) : ⁅y, z⁆ = 0 :=
  (LieModule.mem_maxTrivSubmodule ℝ G G z).mp hz y

end X7Z10C

open X7Z10C in
theorem X7_centralQuadratic_recession {G : Type*} [LieRing G] [LieAlgebra ℝ G]
    [FiniteDimensional ℝ G] (P : StructuralPresentation (G := G)) (x : G) :
    centralQuadraticCone P x ⊆ recession (orbitHull x) ∩ (LieAlgebra.center ℝ G : Set G) := by
  set K := orbitHull x with hKdef
  have hKc : IsClosed K := isClosed_closure
  have hKv : Convex ℝ K := (convex_convexHull ℝ _).closure
  have horb : innerAdjointOrbit x ⊆ K := fun y hy => subset_closure (subset_convexHull ℝ _ hy)
  set l : G := lPart P x with hl
  -- the generators are central
  have hgen_c : ∀ v : P.V, ⁅(v : G), ⁅(v : G), l⁆⁆ ∈ LieAlgebra.center ℝ G := by
    intro v
    have h1 : ⁅l, (v : G)⁆ ∈ P.V := P.lv_bracket (P.coordinates x).2.2 v
    have h2 : ⁅(v : G), l⁆ ∈ P.V := by
      rw [← lie_skew]; exact P.V.neg_mem h1
    exact P.v_bracket v ⟨_, h2⟩
  -- the generators are recession directions
  have hgen_r : ∀ v : P.V, ⁅(v : G), ⁅(v : G), l⁆⁆ ∈ recession K := by
    intro v
    set g := ⁅(v : G), ⁅(v : G), l⁆⁆ with hg
    set a := ⁅(v : G), x⁆ with ha
    have hva : ⁅(v : G), a⁆ = g := by
      have hx := P.reconstruct x
      have hz : ((P.coordinates x).1 : G) ∈ LieAlgebra.center ℝ G := (P.coordinates x).1.2
      have hw : ⁅(v : G), ((P.coordinates x).2.1 : G)⁆ ∈ LieAlgebra.center ℝ G :=
        P.v_bracket v (P.coordinates x).2.1
      rw [ha, ← hx]
      simp only [lie_add, X7_center_bracket hz, X7_center_bracket hw, zero_add, lie_zero]
      rfl
    have hvg : ⁅(v : G), g⁆ = 0 := X7_center_bracket (hgen_c v) _
    -- orbit points
    have hq : ∀ t : ℝ, x + t • a + (t ^ 2 / 2) • g ∈ K := by
      intro t
      apply horb
      refine ⟨[t • (v : G)], ?_⟩
      have hN : ∀ y : G, (LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ G (t • (v : G)))) y =
          t • ⁅(v : G), y⁆ := by
        intro y
        simp [smul_lie]
      simp only [innerWord, List.foldr_cons, List.foldr_nil, ContinuousLinearMap.comp_id]
      rw [X7_exp3]
      · rw [hN, hN, lie_smul, hva]
        rw [smul_smul]
        congr 1
        rw [smul_smul]
        congr 1
        ring
      · simp only [hN, lie_smul]
        rw [← ha, hva, hvg]
        simp
    intro y hy
    -- sequence of convex combinations
    let t : ℕ → ℝ := fun n => (n : ℝ) + 2
    have ht2 : ∀ n, 2 ≤ t n := fun n => by simp [t]
    have htpos : ∀ n, 0 < t n := fun n => by linarith [ht2 n]
    let p : ℕ → G := fun n =>
      (1 - 2 / t n ^ 2) • y + (2 / t n ^ 2) • (x + t n • a + (t n ^ 2 / 2) • g)
    have hpK : ∀ n, p n ∈ K := by
      intro n
      have hl1 : 2 / t n ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith [ht2 n]
      exact hKv hy (hq (t n)) (by linarith) (by positivity) (by ring)
    have hpeq : ∀ n, p n = y + g + (2 * (1 / t n) ^ 2) • (x - y) + (2 * (1 / t n)) • a := by
      intro n
      have hne : t n ≠ 0 := (htpos n).ne'
      simp only [p, smul_add, smul_smul, sub_smul, one_smul, smul_sub]
      have e1 : 2 / t n ^ 2 * t n = 2 * (1 / t n) := by field_simp
      have e2 : 2 / t n ^ 2 * (t n ^ 2 / 2) = 1 := by field_simp
      have e3 : 2 / t n ^ 2 = 2 * (1 / t n) ^ 2 := by field_simp
      rw [e1, e2, e3, one_smul]
      abel
    have hu : Tendsto (fun n => 1 / t n) atTop (𝓝 0) := by
      apply tendsto_const_nhds.div_atTop
      exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have hlim : Tendsto p atTop (𝓝 (y + g)) := by
      have h := ((tendsto_const_nhds (x := y + g)).add
        (((hu.pow 2).const_mul 2).smul_const (x - y))).add ((hu.const_mul 2).smul_const a)
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_smul,
        add_zero] at h
      refine h.congr ?_
      intro n
      rw [hpeq n]
    exact hKc.mem_of_tendsto hlim (Eventually.of_forall hpK)
  -- the intersection is a closed cone
  have hcone : ClosedCone (recession K ∩ (LieAlgebra.center ℝ G : Set G)) := by
    have hZc : IsClosed ((LieAlgebra.center ℝ G).toSubmodule : Set G) :=
      Submodule.closed_of_finiteDimensional _
    refine ⟨(X7_rec_closed K hKc).inter hZc,
      (X7_rec_convex K hKv).inter (LieAlgebra.center ℝ G).toSubmodule.convex,
      ⟨fun y hy => by simpa using hy, (LieAlgebra.center ℝ G).zero_mem⟩, ?_⟩
    intro s hs u hu
    exact ⟨X7_rec_smul K hKv u hu.1 s hs, (LieAlgebra.center ℝ G).toSubmodule.smul_mem s hu.2⟩
  intro c hc
  apply hc
  refine ⟨hcone, ?_⟩
  rintro _ ⟨v, rfl⟩
  exact ⟨hgen_r v, hgen_c v⟩

end

end QAlgorithms.Papers.Independent.Frontier30.P26

noncomputable section

open Set

open QAlgorithms.Papers.Independent.Dependency50.P12.Coordinates (expAd)

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] QAlgorithms.Papers.Independent.Frontier30.P26.lieNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Frontier30.P26.lieNormedSpace

open QAlgorithms.Papers.Independent.Frontier30.P26 in
theorem solution {G : Type*} [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G]
    (P : StructuralPresentation (G := G))
    (ha : LieAdmissible (G := G)) (x : G) :
    centralQuadraticCone P x ⊆ recession (orbitHull x) ∩ (LieAlgebra.center ℝ G : Set G) :=
  X7_centralQuadratic_recession P x

end
