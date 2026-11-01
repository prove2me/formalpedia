-- Prove2me | solution 1 for RevConvexDisj.MultiTerm.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T14:11:08.311723+00:00
-- url     : https://prove2.me/submissions/2f58e197-8bd0-4ad4-ab13-8b671db5ae06

import Mathlib
import Definitions.Def_RevConvexDisj_MultiTerm_Model

open scoped Pointwise

namespace RevConvexDisj.MultiTerm.T5Aux

open RevConvexDisj.MultiTerm

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The recession cone is a convex cone -/

lemma recc_zero (C : Set (ι → ℝ)) : (0 : ι → ℝ) ∈ recc C := by
  intro x hx t _
  simpa using hx

lemma recc_add {C : Set (ι → ℝ)} {d e : ι → ℝ} (hd : d ∈ recc C) (he : e ∈ recc C) :
    d + e ∈ recc C := by
  intro x hx t ht
  have := he _ (hd x hx t ht) t ht
  simpa [smul_add, add_assoc] using this

lemma recc_smul {C : Set (ι → ℝ)} {d : ι → ℝ} (hd : d ∈ recc C) {s : ℝ} (hs : 0 ≤ s) :
    s • d ∈ recc C := by
  intro x hx t ht
  have := hd x hx (t * s) (mul_nonneg ht hs)
  simpa [smul_smul] using this

lemma recc_convex (C : Set (ι → ℝ)) : Convex ℝ (recc C) := by
  intro d hd e he a b ha hb _
  exact recc_add (recc_smul hd ha) (recc_smul he hb)

/-! ### The halfline `(-∞,0] r` -/

lemma nonposRay_mem (r : ι → ℝ) {t : ℝ} (ht : t ≤ 0) : t • r ∈ nonposRay r := ⟨t, ht, rfl⟩

lemma nonposRay_convex (r : ι → ℝ) : Convex ℝ (nonposRay r) := by
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩ a b ha hb _
  refine ⟨a * s + b * t, by nlinarith, ?_⟩
  simp [smul_smul, add_smul]

/-! ### Basic facts on the index sets -/

lemma N2_sub_N0c (D : BasisData ι) (C : Set (ι → ℝ)) {j : ι} (hj : j ∈ N2 D C) :
    j ∈ N0c D C := Finset.mem_union_right _ hj

lemma mem_N2 {D : BasisData ι} {C : Set (ι → ℝ)} {j : ι} (hj : j ∈ N2 D C) :
    0 < alpha D C j ∧ alpha D C j < ⊤ ∧ alpha D C j < beta D C j ∧ beta D C j < ⊤ := by
  classical
  unfold N2 at hj
  convert (Finset.mem_filter.mp hj).2

lemma mem_N1 {D : BasisData ι} {C : Set (ι → ℝ)} {j : ι} (hj : j ∈ N1 D C) :
    0 < alpha D C j ∧ alpha D C j < ⊤ ∧ beta D C j = ⊤ := by
  classical
  unfold N1 at hj
  convert (Finset.mem_filter.mp hj).2

lemma mem_N0c {D : BasisData ι} {C : Set (ι → ℝ)} {j : ι} (hj : j ∈ N0c D C) :
    j ∈ N1 D C ∨ j ∈ N2 D C := Finset.mem_union.mp hj

/-- The convex hull `conv(⋃_{j ∈ N^c_0} (α_j, β_j) r̄^j)`. -/
noncomputable def H (D : BasisData ι) (C : Set (ι → ℝ)) : Set (ι → ℝ) :=
  convexHull ℝ (⋃ j ∈ N0c D C, openSeg (alpha D C j) (beta D C j) (D.ray j))

lemma smul_mem_H {D : BasisData ι} {C : Set (ι → ℝ)} {j : ι} (hj : j ∈ N0c D C) {t : ℝ}
    (h1 : alpha D C j < t) (h2 : (t : EReal) < beta D C j) : t • D.ray j ∈ H D C := by
  apply subset_convexHull
  exact Set.mem_iUnion₂.mpr ⟨j, hj, t, h1, h2, rfl⟩

/-! ### Observation (p. 5): `r̄^j ∈ recc(C)` for `j ∈ N1` -/

lemma ray_mem_recc_of_N1 (D : BasisData ι) (C : Set (ι → ℝ)) (hCopen : IsOpen C)
    (hCconv : Convex ℝ C) {j : ι} (hj : j ∈ N1 D C) : D.ray j ∈ recc C := by
  have hb := (mem_N1 hj).2.2
  set r := D.ray j
  -- the set of real `t ≥ 0` with `x̄ + t r ∈ C` is unbounded above
  have hunb : ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ D.xbar + t • r ∈ C ∧ M < t := by
    intro M
    by_contra hcon
    push Not at hcon
    have : beta D C j ≤ (M : EReal) := by
      unfold beta
      apply sSup_le
      rintro _ ⟨t, ⟨ht0, htC⟩, rfl⟩
      show ((t : ℝ) : EReal) ≤ (M : EReal)
      exact_mod_cast hcon t ht0 htC
    rw [hb] at this
    exact absurd this (by simp)
  intro z hz s hs
  rcases hs.eq_or_lt with rfl | hs
  · simpa using hz
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hCopen z hz
  obtain ⟨T, hT0, hTC, hTM⟩ := hunb (s + s * ‖z - D.xbar‖ / ε + 1)
  have hsT : s < T := by
    have : 0 ≤ s * ‖z - D.xbar‖ / ε := by positivity
    linarith
  set θ : ℝ := s / T with hθ
  have hTpos : 0 < T := lt_trans hs hsT
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one hTpos]; exact hsT
  set z' : ι → ℝ := z + (θ / (1 - θ)) • (z - D.xbar) with hz'
  have hz'C : z' ∈ C := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, hz', add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (div_nonneg hθ0 (by linarith))]
    have hq : θ / (1 - θ) = s / (T - s) := by
      rw [hθ]; field_simp
    rw [hq, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    have h1 : s * ‖z - D.xbar‖ / ε < T - s := by linarith
    rw [div_lt_iff₀ hε] at h1
    linarith
  have key : (1 - θ) • z' + θ • (D.xbar + T • r) = z + s • r := by
    have hθT : θ * T = s := by rw [hθ]; field_simp
    have h1θ : (1 - θ) ≠ 0 := by linarith
    rw [hz', smul_add, smul_smul, mul_div_cancel₀ _ h1θ, smul_add, smul_smul, hθT]
    module
  rw [← key]
  exact hCconv hz'C hTC (by linarith) hθ0 (by ring)

/-! ### Inclusions between the convex hulls -/

/-- For `k ∈ N2`, `H ⊆ conv(⋃_{j∈N2} [0,β_j) r̄^j) + recc(C)`. -/
lemma H_sub_icoHull_add_recc (D : BasisData ι) (C : Set (ι → ℝ)) (hCopen : IsOpen C)
    (hCconv : Convex ℝ C) {k : ι} (hk : k ∈ N2 D C) :
    H D C ⊆ convexHull ℝ (⋃ j ∈ N2 D C, icoSeg (beta D C j) (D.ray j)) + recc C := by
  apply convexHull_min _ ((convex_convexHull ℝ _).add (recc_convex C))
  intro x hx
  obtain ⟨j, hj, t, h1, h2, rfl⟩ := Set.mem_iUnion₂.mp hx
  rcases mem_N0c hj with hj1 | hj2
  · -- `j ∈ N1`: `t r̄^j ∈ recc C`, and `0` lies in the hull
    have hα := (mem_N1 hj1).1
    have ht0 : 0 ≤ t := by
      have : ((0 : ℝ) : EReal) < t := lt_trans hα h1
      exact_mod_cast this.le
    have h0 : (0 : ι → ℝ) ∈ convexHull ℝ (⋃ j ∈ N2 D C, icoSeg (beta D C j) (D.ray j)) := by
      apply subset_convexHull
      refine Set.mem_iUnion₂.mpr ⟨k, hk, 0, le_refl _, ?_, by simp⟩
      obtain ⟨hak, -, hab, -⟩ := mem_N2 hk
      exact_mod_cast lt_trans hak hab
    exact ⟨0, h0, t • D.ray j, recc_smul (ray_mem_recc_of_N1 D C hCopen hCconv hj1) ht0,
      zero_add _⟩
  · have hα := (mem_N2 hj2).1
    have ht0 : 0 ≤ t := by
      have : ((0 : ℝ) : EReal) < t := lt_trans hα h1
      exact_mod_cast this.le
    refine ⟨t • D.ray j, subset_convexHull ℝ _ ?_, 0, recc_zero C, add_zero _⟩
    exact Set.mem_iUnion₂.mpr ⟨j, hj2, t, ht0, h2, rfl⟩

/-- For `k ∈ N2`, `conv(⋃_{j∈N2} [0,β_j) r̄^j) ⊆ H + (-∞,0] r̄^k` (the key step of Prop. 5). -/
lemma icoHull_sub_H_add_nonposRay (D : BasisData ι) (C : Set (ι → ℝ)) {k : ι}
    (hk : k ∈ N2 D C) :
    convexHull ℝ (⋃ j ∈ N2 D C, icoSeg (beta D C j) (D.ray j)) ⊆
      H D C + nonposRay (D.ray k) := by
  apply convexHull_min _ ((convex_convexHull ℝ _).add (nonposRay_convex _))
  intro x hx
  obtain ⟨j, hj, t, ht0, ht, rfl⟩ := Set.mem_iUnion₂.mp hx
  by_cases hαt : alpha D C j < t
  · refine ⟨t • D.ray j, smul_mem_H (N2_sub_N0c D C hj) hαt ht, 0, ?_, add_zero _⟩
    simpa using nonposRay_mem (D.ray k) (le_refl (0 : ℝ))
  · push Not at hαt
    obtain ⟨hαj, -, hαβj, -⟩ := mem_N2 hj
    obtain ⟨hαk, -, hαβk, -⟩ := mem_N2 hk
    obtain ⟨l, hl1, hl2⟩ := EReal.lt_iff_exists_real_btwn.mp hαβj
    obtain ⟨μ, hμ1, hμ2⟩ := EReal.lt_iff_exists_real_btwn.mp hαβk
    have htl : t < l := by
      have : (t : EReal) < l := lt_of_le_of_lt hαt hl1
      exact_mod_cast this
    have hl0 : 0 < l := lt_of_le_of_lt ht0 htl
    set θ := t / l with hθ
    have hθ0 : 0 ≤ θ := by positivity
    have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hl0]; exact htl.le
    have hp : θ • (l • D.ray j) + (1 - θ) • (μ • D.ray k) ∈ H D C :=
      convex_convexHull ℝ _ (smul_mem_H (N2_sub_N0c D C hj) hl1 hl2)
        (smul_mem_H (N2_sub_N0c D C hk) hμ1 hμ2) hθ0 (by linarith) (by ring)
    refine ⟨_, hp, (-((1 - θ) * μ)) • D.ray k, nonposRay_mem _ ?_, ?_⟩
    · have : 0 < μ := by
        have : ((0 : ℝ) : EReal) < μ := lt_trans hαk hμ1
        exact_mod_cast this
      nlinarith
    · have hθl : θ * l = t := by rw [hθ]; field_simp
      rw [smul_smul, hθl]
      module

/-- `conv(⋃_{j∈N^c_0} (α_j,+∞) r̄^j) ⊆ {h + ∑_{k∈N2} a_k r̄^k : h ∈ H, a ≥ 0}`. -/
lemma topHull_sub (D : BasisData ι) (C : Set (ι → ℝ)) :
    convexHull ℝ (⋃ j ∈ N0c D C, openSeg (alpha D C j) ⊤ (D.ray j)) ⊆
      {y | ∃ h ∈ H D C, ∃ a : ι → ℝ, (∀ k, 0 ≤ a k) ∧
        y = h + ∑ k ∈ N2 D C, a k • D.ray k} := by
  apply convexHull_min
  · intro x hx
    obtain ⟨j, hj, t, h1, -, rfl⟩ := Set.mem_iUnion₂.mp hx
    by_cases htb : (t : EReal) < beta D C j
    · exact ⟨t • D.ray j, smul_mem_H hj h1 htb, 0, fun _ => le_refl _, by simp⟩
    · push Not at htb
      rcases mem_N0c hj with hj1 | hj2
      · rw [(mem_N1 hj1).2.2] at htb
        exact absurd htb (by simp)
      · obtain ⟨-, -, hαβ, -⟩ := mem_N2 hj2
        obtain ⟨l, hl1, hl2⟩ := EReal.lt_iff_exists_real_btwn.mp hαβ
        have hlt : l ≤ t := by
          have : (l : EReal) ≤ t := (lt_of_lt_of_le hl2 htb).le
          exact_mod_cast this
        refine ⟨l • D.ray j, smul_mem_H hj hl1 hl2, fun k => if k = j then t - l else 0,
          fun k => by dsimp only; split_ifs <;> linarith, ?_⟩
        simp only [ite_smul, zero_smul, Finset.sum_ite_eq', hj2, if_true]
        rw [← add_smul]
        congr 1
        ring
  · rintro _ ⟨h1, hh1, a1, ha1, rfl⟩ _ ⟨h2, hh2, a2, ha2, rfl⟩ p q hp hq hpq
    refine ⟨p • h1 + q • h2, convex_convexHull ℝ _ hh1 hh2 hp hq hpq,
      fun k => p * a1 k + q * a2 k,
      fun k => add_nonneg (mul_nonneg hp (ha1 k)) (mul_nonneg hq (ha2 k)), ?_⟩
    simp only [smul_add, Finset.smul_sum, add_smul, smul_smul, Finset.sum_add_distrib]
    abel

/-! ### The combination step (Lemma 2 in the paper) -/

/-- If `y = m₀ + ∑_{k∈s} a_k r_k` with `a ≥ 0` and, for each `k ∈ s`, `y = m_k - η_k r_k` with
`η_k ≥ 0`, all `m`'s in a convex set `M`, then `y ∈ M`. -/
lemma combine {V : Type*} [AddCommGroup V] [Module ℝ V] {κ : Type*} (M : Set V)
    (hM : Convex ℝ M) (s : Finset κ) (r : κ → V) (y m0 : V) (hm0 : m0 ∈ M) (a : κ → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hy : y = m0 + ∑ k ∈ s, a k • r k)
    (hk : ∀ k ∈ s, ∃ m ∈ M, ∃ η : ℝ, 0 ≤ η ∧ y = m - η • r k) : y ∈ M := by
  classical
  by_cases hex : ∃ k ∈ s, ∃ m ∈ M, y = m - (0 : ℝ) • r k
  · obtain ⟨k, -, m, hm, rfl⟩ := hex
    simpa using hm
  push Not at hex
  have hk' : ∀ k ∈ s, ∃ m ∈ M, ∃ η : ℝ, 0 < η ∧ y = m - η • r k := by
    intro k hks
    obtain ⟨m, hm, η, hη, hy⟩ := hk k hks
    refine ⟨m, hm, η, lt_of_le_of_ne hη ?_, hy⟩
    rintro rfl
    exact hex k hks m hm hy
  choose! m hm η hη hym using hk'
  set c : κ → ℝ := fun k => a k / η k with hc
  have hc0 : ∀ k ∈ s, 0 ≤ c k := fun k hks => div_nonneg (ha k) (hη k hks).le
  have hterm : ∀ k ∈ s, a k • r k = c k • m k - c k • y := by
    intro k hks
    have hyk := hym k hks
    have : η k • r k = m k - y := by rw [hyk]; abel
    rw [← smul_sub, ← this, smul_smul, hc]
    simp only
    rw [div_mul_cancel₀ _ (hη k hks).ne']
  set S := ∑ k ∈ s, c k with hS
  have hsum : ∑ k ∈ s, a k • r k = ∑ k ∈ s, c k • m k - S • y := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, hS, Finset.sum_smul]
  have hmain : (1 + S) • y = m0 + ∑ k ∈ s, c k • m k := by
    have := hy
    rw [hsum] at this
    rw [add_smul, one_smul]
    nth_rewrite 1 [this]
    abel
  have hS0 : 0 ≤ S := Finset.sum_nonneg hc0
  rcases hS0.eq_or_lt with hS0 | hSpos
  · -- all `c k = 0`
    have hzero : ∀ k ∈ s, c k = 0 := (Finset.sum_eq_zero_iff_of_nonneg hc0).mp hS0.symm
    have : ∑ k ∈ s, c k • m k = 0 :=
      Finset.sum_eq_zero fun k hks => by rw [hzero k hks, zero_smul]
    rw [← hS0, this, add_zero, add_zero, one_smul] at hmain
    rw [hmain]; exact hm0
  · have hz : s.centerMass c m ∈ M := hM.centerMass_mem hc0 (by rw [← hS]; exact hSpos)
      (fun k hks => hm k hks)
    have hcomb := hM hm0 hz (show 0 ≤ 1 / (1 + S) by positivity)
      (show 0 ≤ S / (1 + S) by positivity) (by field_simp)
    convert hcomb using 1
    rw [Finset.centerMass, ← hS, smul_smul]
    have h1S : (1 + S) ≠ 0 := by positivity
    have hSne : S ≠ 0 := hSpos.ne'
    have : S / (1 + S) * S⁻¹ = 1 / (1 + S) := by field_simp
    rw [this, ← smul_add, ← hmain, smul_smul]
    field_simp
    simp

/-! ### Theorem 5 -/

lemma TC_sub_SC0 (D : BasisData ι) (C : Set (ι → ℝ)) : TC D C ⊆ SC0 D C := by
  unfold TC T SC0
  gcongr with j hj
  rintro _ ⟨t, h1, h2, rfl⟩
  exact ⟨t, h1, EReal.coe_lt_top t, rfl⟩

lemma TC_sub_SCk (D : BasisData ι) (C : Set (ι → ℝ)) (hCopen : IsOpen C)
    (hCconv : Convex ℝ C) {k : ι} (hk : k ∈ N2 D C) : TC D C ⊆ SCk D C k := by
  rintro _ ⟨_, ⟨_, rfl, h, hh, rfl⟩, q, hq, rfl⟩
  obtain ⟨c, hc, q', hq', rfl⟩ := H_sub_icoHull_add_recc D C hCopen hCconv hk hh
  refine ⟨_, ⟨_, ⟨_, rfl, c, hc, rfl⟩, 0, ?_, rfl⟩, q' + q, recc_add hq' hq, ?_⟩
  · simpa using nonposRay_mem (D.ray k) (le_refl (0 : ℝ))
  · simp [add_assoc]

lemma iInter_sub_TC (D : BasisData ι) (C : Set (ι → ℝ)) :
    SC0 D C ∩ (⋂ k ∈ N2 D C, SCk D C k) ⊆ TC D C := by
  rintro x ⟨hx0, hxk⟩
  rw [Set.mem_iInter₂] at hxk
  set M := H D C + recc C
  have hM : Convex ℝ M := (convex_convexHull ℝ _).add (recc_convex C)
  obtain ⟨_, ⟨_, rfl, g, hg, rfl⟩, q, hq, rfl⟩ := hx0
  obtain ⟨h, hh, a, ha, rfl⟩ := topHull_sub D C hg
  have hy : h + ∑ k ∈ N2 D C, a k • D.ray k + q ∈ M := by
    apply combine M hM (N2 D C) D.ray _ (h + q) ⟨h, hh, q, hq, rfl⟩ a ha (by abel)
    intro k hk
    obtain ⟨_, ⟨_, ⟨_, rfl, c, hc, rfl⟩, n, hn, rfl⟩, q', hq', hxe⟩ := hxk k hk
    obtain ⟨h', hh', _, ⟨t', ht', rfl⟩, rfl⟩ := icoHull_sub_H_add_nonposRay D C hk hc
    obtain ⟨t, ht, rfl⟩ := hn
    refine ⟨h' + q', ⟨h', hh', q', hq', rfl⟩, -(t' + t), by linarith, ?_⟩
    simp only at hxe
    rw [neg_smul, sub_neg_eq_add, add_smul]
    calc h + ∑ k ∈ N2 D C, a k • D.ray k + q
        = (D.xbar + (h + ∑ k ∈ N2 D C, a k • D.ray k) + q) - D.xbar := by abel
      _ = (D.xbar + (h' + t' • D.ray k) + t • D.ray k + q') - D.xbar := by rw [hxe]
      _ = h' + q' + (t' • D.ray k + t • D.ray k) := by abel
  obtain ⟨h0, hh0, q0, hq0, he⟩ := hy
  refine ⟨D.xbar + h0, ⟨D.xbar, rfl, h0, hh0, rfl⟩, q0, hq0, ?_⟩
  simp only at he
  show D.xbar + h0 + q0 = D.xbar + (h + ∑ k ∈ N2 D C, a k • D.ray k) + q
  rw [add_assoc, he]
  abel

lemma TC_eq (D : BasisData ι) (C : Set (ι → ℝ)) (hCopen : IsOpen C) (hCconv : Convex ℝ C) :
    TC D C = SC0 D C ∩ ⋂ k ∈ N2 D C, SCk D C k := by
  apply Set.Subset.antisymm
  · exact Set.subset_inter (TC_sub_SC0 D C)
      (Set.subset_iInter₂ fun k hk => TC_sub_SCk D C hCopen hCconv hk)
  · exact iInter_sub_TC D C

end RevConvexDisj.MultiTerm.T5Aux

open RevConvexDisj.MultiTerm in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : BasisData ι) (C : Set (ι → ℝ))
    (hCopen : IsOpen C) (hCconv : Convex ℝ C) (hxbar : D.xbar ∉ closure C)
    (hA2 : recc C ⊆ recc D.PB) :
    D.PB \ TC D C = (D.PB \ SC0 D C) ∪ ⋃ k ∈ N2 D C, (D.PB \ SCk D C k) := by
  rw [RevConvexDisj.MultiTerm.T5Aux.TC_eq D C hCopen hCconv]
  ext x
  simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_union, Set.mem_iUnion]
  constructor
  · rintro ⟨hP, hn⟩
    by_cases h0 : x ∈ SC0 D C
    · right
      push Not at hn
      obtain ⟨k, hk, hxk⟩ := hn h0
      exact ⟨k, hk, hP, hxk⟩
    · exact Or.inl ⟨hP, h0⟩
  · rintro (⟨hP, h0⟩ | ⟨k, hk, hP, hxk⟩)
    · exact ⟨hP, fun h => h0 h.1⟩
    · exact ⟨hP, fun h => hxk (h.2 k hk)⟩
