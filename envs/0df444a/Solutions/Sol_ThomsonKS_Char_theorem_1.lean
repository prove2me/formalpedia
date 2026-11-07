-- Prove2me | solution 1 for ThomsonKS.Char.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T12:35:53.645399+00:00
-- url     : https://prove2.me/submissions/f0b37356-e258-4e09-9d73-10406be929a7

import Mathlib
import Definitions.Def_ThomsonKS_Char_Setting

open ThomsonKS.Char Filter Topology
open scoped Pointwise

namespace KSThm1

variable {P : Finset ℕ}

lemma bdd {S : Set (P → ℝ)} (hS : S ∈ DivProb P) (i : P) :
    BddAbove ((fun x : P → ℝ => x i) '' S) :=
  (hS.2.2.1.image (continuous_apply i)).bddAbove

lemma nonempty {S : Set (P → ℝ)} (hS : S ∈ DivProb P) : S.Nonempty := by
  obtain ⟨x0, hx0, -⟩ := hS.2.2.2.2.1
  exact ⟨x0, hx0⟩

lemma le_ideal {S : Set (P → ℝ)} (hS : S ∈ DivProb P) {x : P → ℝ}
    (hx : x ∈ S) (i : P) : x i ≤ idealPt S i :=
  le_csSup (bdd hS i) ⟨x, hx, rfl⟩

lemma ideal_le {S : Set (P → ℝ)} (hS : S ∈ DivProb P) {i : P} {r : ℝ}
    (h : ∀ x ∈ S, x i ≤ r) : idealPt S i ≤ r := by
  apply csSup_le ((nonempty hS).image _)
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

lemma ideal_attained {S : Set (P → ℝ)} (hS : S ∈ DivProb P) (i : P) :
    ∃ x ∈ S, x i = idealPt S i := by
  have hc : IsCompact ((fun x : P → ℝ => x i) '' S) := hS.2.2.1.image (continuous_apply i)
  obtain ⟨x, hx, h⟩ := hc.sSup_mem ((nonempty hS).image _)
  exact ⟨x, hx, h⟩

lemma ideal_pos {S : Set (P → ℝ)} (hS : S ∈ DivProb P) (i : P) : 0 < idealPt S i := by
  obtain ⟨x0, hx0, hx0p⟩ := hS.2.2.2.2.1
  exact lt_of_lt_of_le (hx0p i) (le_ideal hS hx0 i)

lemma zero_mem {S : Set (P → ℝ)} (hS : S ∈ DivProb P) : (0 : P → ℝ) ∈ S := by
  obtain ⟨x0, hx0, hx0p⟩ := hS.2.2.2.2.1
  exact hS.2.2.2.2.2 x0 hx0 0 le_rfl (fun i => (hx0p i).le)

/-- the set of admissible `t`. -/
def tset (S : Set (P → ℝ)) : Set ℝ := {t : ℝ | 0 ≤ t ∧ t • idealPt S ∈ S}

lemma tset_bdd {S : Set (P → ℝ)} (hS : S ∈ DivProb P) : BddAbove (tset S) := by
  refine ⟨1, ?_⟩
  rintro t ⟨ht0, ht⟩
  obtain ⟨i, hi⟩ := hS.1
  have h1 := le_ideal hS ht ⟨i, hi⟩
  have h2 := ideal_pos hS ⟨i, hi⟩
  simp only [Pi.smul_apply, smul_eq_mul] at h1
  nlinarith

lemma tset_closed {S : Set (P → ℝ)} (hS : S ∈ DivProb P) : IsClosed (tset S) := by
  have : tset S = {t : ℝ | 0 ≤ t} ∩ (fun t : ℝ => t • idealPt S) ⁻¹' S := rfl
  rw [this]
  exact (isClosed_le continuous_const continuous_id).inter
    (hS.2.2.1.isClosed.preimage (continuous_id.smul continuous_const))

lemma tset_nonempty {S : Set (P → ℝ)} (hS : S ∈ DivProb P) : (tset S).Nonempty :=
  ⟨0, le_rfl, by simpa using zero_mem hS⟩

lemma tstar_mem {S : Set (P → ℝ)} (hS : S ∈ DivProb P) : sSup (tset S) ∈ tset S :=
  (tset_closed hS).csSup_mem (tset_nonempty hS) (tset_bdd hS)

lemma le_tstar {S : Set (P → ℝ)} (hS : S ∈ DivProb P) {s : ℝ} (hs : s ∈ tset S) :
    s ≤ sSup (tset S) := le_csSup (tset_bdd hS) hs

lemma KS_eq (S : Set (P → ℝ)) : KS P S = sSup (tset S) • idealPt S := rfl

lemma KS_image {P' : Finset ℕ} (g : (P → ℝ) → (P' → ℝ)) (hg : Function.Injective g)
    (hsmul : ∀ (t : ℝ) x, g (t • x) = t • g x) (S : Set (P → ℝ))
    (ha : idealPt (g '' S) = g (idealPt S)) : KS P' (g '' S) = g (KS P S) := by
  rw [KS_eq, KS_eq, ha]
  have : tset (g '' S) = tset S := by
    ext t
    simp only [tset, Set.mem_setOf_eq, ha, ← hsmul, hg.mem_set_image]
  rw [this, hsmul]

lemma idealPt_scale (S : Set (P → ℝ)) {c : P → ℝ} (hc : ∀ i, 0 < c i) :
    idealPt (scale c '' S) = scale c (idealPt S) := by
  funext i
  simp only [idealPt, scale]
  rw [Set.image_image]
  have : (fun x : P → ℝ => scale c x i) '' S = c i • ((fun x : P → ℝ => x i) '' S) := by
    rw [← Set.image_smul, Set.image_image]; rfl
  rw [this, Real.sSup_smul_of_nonneg (hc i).le, smul_eq_mul]

lemma relabel_eq {P' : Finset ℕ} (γ : P ≃ P') (S : Set (P → ℝ)) :
    relabel γ S = (fun x : P → ℝ => fun i' => x (γ.symm i')) '' S := by
  ext x'
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, funext fun i' => ?_⟩
    have := h (γ.symm i')
    simp only [Equiv.apply_symm_apply] at this
    exact this.symm
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, fun i => by simp⟩

/-- `near A B δ`: every point of `A` is within `δ` (coordinatewise) of a point of `B`. -/
def near (A B : Set (P → ℝ)) (δ : ℝ) : Prop :=
  ∀ x ∈ A, ∃ y ∈ B, ∀ i, |x i - y i| < δ

lemma near_of_hd {A B : Set (P → ℝ)} {δ : ℝ}
    (h : Metric.hausdorffEDist A B < ENNReal.ofReal δ) : near A B δ := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Metric.exists_edist_lt_of_hausdorffEDist_lt hx h
  refine ⟨y, hy, fun i => ?_⟩
  rw [edist_lt_ofReal] at hxy
  have := dist_le_pi_dist x y i
  rw [Real.dist_eq] at this
  linarith

lemma ideal_near {A B : Set (P → ℝ)} (hA : A ∈ DivProb P) (hB : B ∈ DivProb P) {δ : ℝ}
    (h : near A B δ) (i : P) : idealPt A i ≤ idealPt B i + δ := by
  apply ideal_le hA
  intro x hx
  obtain ⟨y, hy, hxy⟩ := h x hx
  have h1 := le_ideal hB hy i
  have h2 := (abs_lt.mp (hxy i)).2
  linarith

lemma eventually_near {Sk : ℕ → Set (P → ℝ)} {S : Set (P → ℝ)}
    (ht : Tendsto (fun k => Metric.hausdorffEDist (Sk k) S) atTop (𝓝 0)) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k in atTop, near (Sk k) S δ ∧ near S (Sk k) δ := by
  have hpos : (0 : ENNReal) < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ
  filter_upwards [(tendsto_order.1 ht).2 _ hpos] with k hk
  refine ⟨near_of_hd hk, near_of_hd ?_⟩
  rwa [Metric.hausdorffEDist_comm]

end KSThm1

open KSThm1

theorem solution : IsSolution KS ∧ WPO KS ∧ An KS ∧ SInv KS ∧ Cont KS ∧ Mon KS := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  -- IsSolution
  · intro P S hS
    exact (tstar_mem hS).2
  -- WPO
  · intro P S hS y hy hlt hyS
    set t := sSup (tset S)
    set a := idealPt S
    have hU : IsOpen {s : ℝ | ∀ i, s * a i < y i} := by
      have : {s : ℝ | ∀ i, s * a i < y i} = ⋂ i, {s : ℝ | s * a i < y i} := by
        ext s; simp
      rw [this]
      exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_id.mul continuous_const)
        continuous_const
    have htU : t ∈ {s : ℝ | ∀ i, s * a i < y i} := by
      intro i; have := hlt i; rw [KS_eq] at this; simpa using this
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU t htU
    have hs : t + ε / 2 ∈ {s : ℝ | ∀ i, s * a i < y i} := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      rw [abs_of_pos (by linarith : (0:ℝ) < t + ε / 2 - t)]; linarith
    have ht0 : 0 ≤ t := (tstar_mem hS).1
    have hmem : t + ε / 2 ∈ tset S := by
      refine ⟨by linarith, hS.2.2.2.2.2 y hyS _ ?_ ?_⟩
      · intro i; simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        exact mul_nonneg (by linarith) (ideal_pos hS i).le
      · intro i; simp only [Pi.smul_apply, smul_eq_mul]; exact (hs i).le
    have := le_tstar hS hmem
    linarith
  -- An
  · intro P P' γ S hS S' hS' hrel i
    subst hrel
    have hrel' := relabel_eq γ S
    set g : (P → ℝ) → (P' → ℝ) := fun x i' => x (γ.symm i') with hg
    have hginj : Function.Injective g := by
      intro x y hxy
      funext i
      have := congrFun hxy (γ i)
      simpa [hg] using this
    have ha : idealPt (g '' S) = g (idealPt S) := by
      funext i'
      simp only [idealPt, hg, Set.image_image]
    rw [hrel', KS_image g hginj (fun t x => rfl) S ha]
    simp [hg]
  -- SInv
  · intro P S hS c hc
    have hinj : Function.Injective (scale c) := by
      intro x y hxy
      funext i
      have := congrFun hxy i
      simp only [scale] at this
      exact mul_left_cancel₀ (hc i).ne' this
    exact KS_image (scale c) hinj (fun t x => by funext i; simp [scale]; ring) S
      (idealPt_scale S hc)
  -- Cont
  · intro P Sk S hS hSk ht
    set a := idealPt S
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : P, ∀ i, a i₀ ≤ a i := by
      haveI : Nonempty P := by obtain ⟨i, hi⟩ := hS.1; exact ⟨⟨i, hi⟩⟩
      exact Finite.exists_min a
    set m := a i₀
    have hm : 0 < m := ideal_pos hS i₀
    set t := sSup (tset S)
    have ht0 : 0 ≤ t := (tstar_mem hS).1
    -- convergence of ideal points
    have ha : Tendsto (fun k => idealPt (Sk k)) atTop (𝓝 a) := by
      rw [tendsto_pi_nhds]
      intro i
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_near ht (half_pos hε))
      refine ⟨N, fun k hk => ?_⟩
      obtain ⟨h1, h2⟩ := hN k hk
      have e1 := ideal_near (hSk k) hS h1 i
      have e2 := ideal_near hS (hSk k) h2 i
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    -- convergence of the t's
    have htk : Tendsto (fun k => sSup (tset (Sk k))) atTop (𝓝 t) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      set δ : ℝ := min (ε * m / (4 * (t + ε + 1))) m with hδ_def
      have hδpos : 0 < δ := lt_min (by positivity) hm
      have hδm : δ ≤ m := min_le_right _ _
      have hδ1 : δ ≤ ε * m / (4 * (t + ε + 1)) := min_le_left _ _
      have hδ1' : δ * (4 * (t + ε + 1)) ≤ ε * m := by
        rwa [le_div_iff₀ (by positivity)] at hδ1
      obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_near ht hδpos)
      refine ⟨N, fun k hk => ?_⟩
      obtain ⟨h1, h2⟩ := hN k hk
      set tk := sSup (tset (Sk k))
      have htk0 : 0 ≤ tk := (tstar_mem (hSk k)).1
      have hak1 : ∀ i, idealPt (Sk k) i ≤ a i + δ := ideal_near (hSk k) hS h1
      have hak2 : ∀ i, a i ≤ idealPt (Sk k) i + δ := ideal_near hS (hSk k) h2
      -- lower bound
      have hlow : t - ε / 2 ≤ tk := by
        by_cases hs : t - ε / 2 ≤ 0
        · linarith
        push Not at hs
        obtain ⟨z, hz, hzt⟩ := h2 _ (tstar_mem hS).2
        have hmem : t - ε / 2 ∈ tset (Sk k) := by
          refine ⟨hs.le, (hSk k).2.2.2.2.2 z hz _ ?_ ?_⟩
          · intro i; simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
            exact mul_nonneg hs.le (ideal_pos (hSk k) i).le
          · intro i
            simp only [Pi.smul_apply, smul_eq_mul]
            have e1 := (abs_lt.mp (hzt i)).2
            simp only [Pi.smul_apply, smul_eq_mul] at e1
            have e2 := hak1 i
            have e3 := hi₀ i
            have e4 : (t - ε / 2) * idealPt (Sk k) i ≤ (t - ε / 2) * (a i + δ) :=
              mul_le_mul_of_nonneg_left e2 hs.le
            have e5 : δ * (1 + t) ≤ ε / 2 * a i := by
              have : δ * (2 * (1 + t)) ≤ ε * a i := by
                nlinarith
              linarith
            nlinarith
        exact le_tstar (hSk k) hmem
      -- upper bound
      have hup : tk ≤ t + ε / 2 := by
        by_contra hcon
        push Not at hcon
        obtain ⟨w, hw, hwt⟩ := h1 _ (tstar_mem (hSk k)).2
        have hmem : t + ε / 4 ∈ tset S := by
          refine ⟨by linarith, hS.2.2.2.2.2 w hw _ ?_ ?_⟩
          · intro i; simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
            exact mul_nonneg (by linarith) (ideal_pos hS i).le
          · intro i
            simp only [Pi.smul_apply, smul_eq_mul]
            have e1 := (abs_lt.mp (hwt i)).2
            simp only [Pi.smul_apply, smul_eq_mul] at e1
            have e2 := hak2 i
            have e3 := hi₀ i
            have e6 : 0 ≤ a i - δ := by linarith
            have e4 : (t + ε / 2) * (a i - δ) ≤ tk * idealPt (Sk k) i :=
              mul_le_mul hcon.le (by linarith) e6 htk0
            have e5 : δ * (t + ε + 1) ≤ ε / 4 * a i := by
              have : δ * (4 * (t + ε + 1)) ≤ ε * a i := by nlinarith
              linarith
            nlinarith
        have := le_tstar hS hmem
        linarith
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have := htk.smul ha
    simpa only [KS_eq] using this
  -- Mon
  · intro P Q hPQ S hS T hT hsl i
    have hS_iff : ∀ x, x ∈ S ↔ zeroExt hPQ x ∈ T := fun x => by rw [hsl]; rfl
    have hab : ∀ j : P, idealPt S j = idealPt T ⟨j, hPQ j.2⟩ := by
      intro j
      apply le_antisymm
      · apply ideal_le hS
        intro x hx
        have := le_ideal hT ((hS_iff x).mp hx) ⟨j, hPQ j.2⟩
        simpa [zeroExt] using this
      · obtain ⟨z, hz, hzj⟩ := ideal_attained hT ⟨j, hPQ j.2⟩
        have hx : (fun l : P => z ⟨l, hPQ l.2⟩) ∈ S := by
          rw [hS_iff]
          refine hT.2.2.2.2.2 z hz _ ?_ ?_
          · intro l; simp only [zeroExt, Pi.zero_apply]
            split_ifs
            · exact hT.2.1 z hz _
            · exact le_rfl
          · intro l; simp only [zeroExt]
            split_ifs
            · exact le_rfl
            · exact hT.2.1 z hz _
        have := le_ideal hS hx j
        rw [← hzj]; exact this
    have htT : sSup (tset T) ∈ tset T := tstar_mem hT
    have hmem : sSup (tset T) ∈ tset S := by
      refine ⟨htT.1, ?_⟩
      rw [hS_iff]
      refine hT.2.2.2.2.2 _ htT.2 _ ?_ ?_
      · intro l; simp only [zeroExt, Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
        split_ifs
        · exact mul_nonneg htT.1 (ideal_pos hS _).le
        · exact le_rfl
      · intro l; simp only [zeroExt, Pi.smul_apply, smul_eq_mul]
        split_ifs with hl
        · rw [hab]
        · exact mul_nonneg htT.1 (ideal_pos hT _).le
    have hle := le_tstar hS hmem
    rw [KS_eq, KS_eq]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← hab i]
    exact mul_le_mul_of_nonneg_right hle (ideal_pos hS i).le
