-- Prove2me | solution 1 for Reiman84.QueueLength.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T18:55:26.291001+00:00
-- url     : https://prove2.me/submissions/cbcee6c7-bcac-4dd9-bb8a-c5be1c694a17

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_HarrisonReimanRBM_Orthant_Basic

namespace RBMOCore

open Reiman84.QueueLength HarrisonReimanRBM.Orthant Filter Topology

/-- BddAbove of a continuous function's values over `Icc 0 t ⊆ Icc 0 T`. -/
lemma bdd_of_contOn {f : ℝ → ℝ} {T t : ℝ} (hf : ContinuousOn f (Set.Icc 0 T)) (ht : t ≤ T) :
    BddAbove (Set.range fun s : Set.Icc (0 : ℝ) t => f s) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.bddAbove_image hf)
  refine ⟨M, ?_⟩
  rintro _ ⟨⟨s, hs⟩, rfl⟩
  exact hM ⟨s, ⟨hs.1, hs.2.trans ht⟩, rfl⟩

lemma abs_ciSup_sub_le {ι : Type*} [Nonempty ι] {f g : ι → ℝ} (hf : BddAbove (Set.range f))
    (hg : BddAbove (Set.range g)) {c : ℝ} (h : ∀ i, |f i - g i| ≤ c) :
    |(⨆ i, f i) - ⨆ i, g i| ≤ c := by
  rw [abs_le]
  constructor
  · have : (⨆ i, g i) ≤ (⨆ i, f i) + c := by
      apply ciSup_le
      intro i
      have h1 := le_ciSup hf i
      have h2 := (abs_le.1 (h i)).1
      linarith
    linarith
  · have : (⨆ i, f i) ≤ (⨆ i, g i) + c := by
      apply ciSup_le
      intro i
      have h1 := le_ciSup hg i
      have h2 := (abs_le.1 (h i)).2
      linarith
    linarith

lemma vecMul_apply' {K : ℕ} (y : Fin K → ℝ) (Q : Matrix (Fin K) (Fin K) ℝ) (j : Fin K) :
    Matrix.vecMul y Q j = ∑ i, y i * Q i j := by
  simp [Matrix.vecMul, dotProduct]

lemma contOn_comp_apply {K : ℕ} {S : Set ℝ} {y : ℝ → Fin K → ℝ} (hy : ContinuousOn y S)
    (j : Fin K) : ContinuousOn (fun t => y t j) S :=
  (continuous_apply j).comp_continuousOn hy

lemma contOn_vecMul {K : ℕ} {S : Set ℝ} {y : ℝ → Fin K → ℝ} (hy : ContinuousOn y S)
    (Q : Matrix (Fin K) (Fin K) ℝ) (j : Fin K) :
    ContinuousOn (fun t => Matrix.vecMul (y t) Q j) S := by
  simp_rw [vecMul_apply']
  exact continuousOn_finsetSum _ (fun i _ => (contOn_comp_apply hy i).mul continuousOn_const)

lemma contOn_inner {K : ℕ} {S : Set ℝ} {x y : ℝ → Fin K → ℝ} (hx : ContinuousOn x S)
    (hy : ContinuousOn y S) (Q : Matrix (Fin K) (Fin K) ℝ) (j : Fin K) :
    ContinuousOn (fun s => max (Matrix.vecMul (y s) Q j - x s j) 0) S :=
  ContinuousOn.sup (ContinuousOn.sub (f := fun s => Matrix.vecMul (y s) Q j)
    (g := fun s => x s j) (contOn_vecMul hy Q j) (contOn_comp_apply hx j)) continuousOn_const

/-- The core weighted bound on `π`. -/
lemma core_bound {K : ℕ} (Q : Matrix (Fin K) (Fin K) ℝ) (hQ0 : ∀ i j, 0 ≤ Q i j)
    (v : Fin K → ℝ) (α : ℝ) (hv : ∀ j, ∑ i, v i * Q i j ≤ α * v j)
    (T : ℝ) (x x' a b : ℝ → Fin K → ℝ)
    (hx : ContinuousOn x (Set.Icc 0 T)) (hx' : ContinuousOn x' (Set.Icc 0 T))
    (ha : ContinuousOn a (Set.Icc 0 T)) (hb : ContinuousOn b (Set.Icc 0 T))
    (D E : ℝ) (hE : 0 ≤ E)
    (hD : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ j, |x s j - x' s j| ≤ D * v j)
    (hab : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i, |a s i - b s i| ≤ E * v i) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ j,
      |piMap Q x a t j - piMap Q x' b t j| ≤ D * v j + α * E * v j := by
  intro t ht j
  have : Nonempty (Set.Icc (0 : ℝ) t) := ⟨⟨0, le_refl 0, ht.1⟩⟩
  unfold piMap
  apply abs_ciSup_sub_le (bdd_of_contOn (contOn_inner hx ha Q j) ht.2)
    (bdd_of_contOn (contOn_inner hx' hb Q j) ht.2)
  rintro ⟨s, hs⟩
  have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
  have h1 : |Matrix.vecMul (a s) Q j - Matrix.vecMul (b s) Q j| ≤ α * E * v j := by
    rw [vecMul_apply', vecMul_apply', ← Finset.sum_sub_distrib]
    calc |∑ i, (a s i * Q i j - b s i * Q i j)| ≤ ∑ i, |a s i * Q i j - b s i * Q i j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, E * (v i * Q i j) := by
          apply Finset.sum_le_sum
          intro i _
          rw [← sub_mul, abs_mul, abs_of_nonneg (hQ0 i j)]
          have := hab s hsT i
          nlinarith [hQ0 i j]
      _ = E * ∑ i, v i * Q i j := by rw [Finset.mul_sum]
      _ ≤ E * (α * v j) := mul_le_mul_of_nonneg_left (hv j) hE
      _ = α * E * v j := by ring
  have h2 := hD s hsT j
  calc |max (Matrix.vecMul (a s) Q j - x s j) 0 - max (Matrix.vecMul (b s) Q j - x' s j) 0|
      ≤ |(Matrix.vecMul (a s) Q j - x s j) - (Matrix.vecMul (b s) Q j - x' s j)| :=
        abs_max_sub_max_le_abs _ _ _
    _ ≤ |Matrix.vecMul (a s) Q j - Matrix.vecMul (b s) Q j| + |x s j - x' s j| := by
        have : (Matrix.vecMul (a s) Q j - x s j) - (Matrix.vecMul (b s) Q j - x' s j)
            = (Matrix.vecMul (a s) Q j - Matrix.vecMul (b s) Q j) - (x s j - x' s j) := by ring
        rw [this]; exact abs_sub _ _
    _ ≤ D * v j + α * E * v j := by linarith

lemma contOn_max0 {w : ℝ → ℝ} {S : Set ℝ} (hw : ContinuousOn w S) :
    ContinuousOn (fun s => max (w s) 0) S :=
  ContinuousOn.sup hw continuousOn_const

/-- One-dimensional Skorokhod lemma, forward direction. -/
lemma skor_fwd (y w z : ℝ → ℝ) (hy : ContinuousOn y (Set.Ici 0))
    (hw : ContinuousOn w (Set.Ici 0)) (hz : ∀ t, 0 ≤ t → z t = y t - w t)
    (hz0 : ∀ t, 0 ≤ t → 0 ≤ z t) (hmono : MonotoneOn y (Set.Ici 0)) (h0 : y 0 = 0)
    (hcomp : ∀ s t : ℝ, 0 ≤ s → s ≤ t → (∀ r ∈ Set.Icc s t, 0 < z r) → y t = y s) :
    ∀ t, 0 ≤ t → y t = ⨆ s : Set.Icc (0 : ℝ) t, max (w s) 0 := by
  intro t ht
  have hwt : ContinuousOn w (Set.Icc 0 t) := hw.mono Set.Icc_subset_Ici_self
  have bdd := bdd_of_contOn (T := t) (contOn_max0 hwt) le_rfl
  have : Nonempty (Set.Icc (0 : ℝ) t) := ⟨⟨0, le_refl 0, ht⟩⟩
  apply le_antisymm
  · by_cases hS : ∃ s ∈ Set.Icc (0 : ℝ) t, z s = 0
    · have hzc : ContinuousOn z (Set.Icc 0 t) := by
        have := (hy.mono Set.Icc_subset_Ici_self).sub hwt
        refine this.congr ?_
        intro r hr; exact hz r hr.1
      set S := Set.Icc (0 : ℝ) t ∩ z ⁻¹' {0} with hSdef
      have hSc : IsClosed S := hzc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
      have hSne : S.Nonempty := by
        obtain ⟨s, hs, hzs⟩ := hS; exact ⟨s, hs, hzs⟩
      have hSb : BddAbove S := ⟨t, fun r hr => hr.1.2⟩
      set m := sSup S with hm
      have hmS : m ∈ S := hSc.csSup_mem hSne hSb
      have hm0 : 0 ≤ m := hmS.1.1
      have hmt : m ≤ t := hmS.1.2
      have hzm : z m = 0 := hmS.2
      have hytm : y t = y m := by
        by_contra hne
        have hlt : y m < y t := lt_of_le_of_ne (hmono hm0 ht hmt) (Ne.symm hne)
        have hmt' : m < t := by
          rcases lt_or_eq_of_le hmt with h | h
          · exact h
          · exact absurd (by rw [h]) hne
        obtain ⟨δ, hδ, hδy⟩ := Metric.continuousWithinAt_iff.1 (hy m hm0) (y t - y m)
          (by linarith)
        set r := min (m + δ / 2) t with hr
        have hmr : m < r := lt_min (by linarith) hmt'
        have hrt : r ≤ t := min_le_right _ _
        have hyr : y t = y r := by
          apply hcomp r t (by linarith) hrt
          intro q hq
          have hq0 : 0 ≤ q := by linarith [hq.1]
          rcases lt_or_eq_of_le (hz0 q hq0) with h | h
          · exact h
          · have hqS : q ∈ S := ⟨⟨hq0, hq.2⟩, h.symm⟩
            have := le_csSup hSb hqS
            linarith [hq.1]
        have hd : dist r m < δ := by
          rw [Real.dist_eq, abs_of_pos (by linarith)]
          have := min_le_left (m + δ / 2) t
          linarith
        have := hδy (show r ∈ Set.Ici (0:ℝ) by simp; linarith) hd
        rw [Real.dist_eq, ← hyr, abs_of_pos (by linarith)] at this
        linarith
      have hym : y m = w m := by have := hz m hm0; linarith
      calc y t = w m := by rw [hytm, hym]
        _ ≤ max (w m) 0 := le_max_left _ _
        _ ≤ _ := le_ciSup bdd (⟨m, hm0, hmt⟩ : Set.Icc (0:ℝ) t)
    · push Not at hS
      have : y t = y 0 := hcomp 0 t le_rfl ht (fun r hr =>
        lt_of_le_of_ne (hz0 r hr.1) (Ne.symm (hS r hr)))
      calc y t = 0 := by rw [this, h0]
        _ ≤ max (w 0) 0 := le_max_right _ _
        _ ≤ _ := le_ciSup bdd (⟨0, le_rfl, ht⟩ : Set.Icc (0:ℝ) t)
  · apply ciSup_le
    rintro ⟨s, hs⟩
    apply max_le
    · have h1 := hz0 s hs.1
      have h2 := hz s hs.1
      have h3 := hmono hs.1 ht hs.2
      simp only; linarith
    · rw [← h0]; exact hmono (Set.mem_Ici.2 le_rfl) ht ht

/-- One-dimensional Skorokhod lemma, backward direction. -/
lemma skor_bwd (y w : ℝ → ℝ) (hy : ContinuousOn y (Set.Ici 0))
    (hw : ContinuousOn w (Set.Ici 0)) (hmono : MonotoneOn y (Set.Ici 0)) (h0 : y 0 = 0)
    (hfix : ∀ t, 0 ≤ t → y t = ⨆ s : Set.Icc (0 : ℝ) t, max (w s) 0) :
    (∀ t, 0 ≤ t → 0 ≤ y t - w t) ∧
    (∀ s t : ℝ, 0 ≤ s → s ≤ t → (∀ r ∈ Set.Icc s t, 0 < y r - w r) → y t = y s) := by
  constructor
  · intro t ht
    have hwt : ContinuousOn w (Set.Icc 0 t) := hw.mono Set.Icc_subset_Ici_self
    have bdd := bdd_of_contOn (T := t) (contOn_max0 hwt) le_rfl
    have := le_ciSup bdd (⟨t, ht, le_rfl⟩ : Set.Icc (0:ℝ) t)
    rw [← hfix t ht] at this
    have := le_max_left (w t) 0
    simp only at *
    linarith
  · intro s t hs hst hpos
    have ht : 0 ≤ t := hs.trans hst
    have hwt : ContinuousOn w (Set.Icc 0 t) := hw.mono Set.Icc_subset_Ici_self
    have bdd := bdd_of_contOn (T := t) (contOn_max0 hwt) le_rfl
    have bdds := bdd_of_contOn (T := t) (contOn_max0 hwt) hst
    have : Nonempty (Set.Icc (0 : ℝ) t) := ⟨⟨0, le_refl 0, ht⟩⟩
    have hle : y s ≤ y t := hmono hs ht hst
    by_contra hne
    have hlt : y s < y t := lt_of_le_of_ne hle (Ne.symm hne)
    obtain ⟨r, hr, hrmax⟩ := isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.2 ht) (contOn_max0 hwt)
    have hsup : (⨆ q : Set.Icc (0 : ℝ) t, max (w q) 0) = max (w r) 0 := by
      apply le_antisymm
      · apply ciSup_le; rintro ⟨q, hq⟩; exact hrmax hq
      · exact le_ciSup bdd (⟨r, hr⟩ : Set.Icc (0:ℝ) t)
    have hyt : y t = max (w r) 0 := by rw [hfix t ht, hsup]
    have hsr : s < r := by
      by_contra hrs
      push Not at hrs
      have := le_ciSup bdds (⟨r, hr.1, hrs⟩ : Set.Icc (0:ℝ) s)
      rw [← hfix s hs] at this
      simp only at this
      linarith
    have hys0 : 0 ≤ y s := by rw [← h0]; exact hmono (Set.mem_Ici.2 le_rfl) hs hs
    have hwr : max (w r) 0 = w r := by
      rcases le_total (w r) 0 with h | h
      · rw [max_eq_right h] at hyt; linarith
      · exact max_eq_left h
    have hyr : y r ≤ y t := hmono (Set.mem_Ici.2 hr.1) ht hr.2
    have := hpos r ⟨hsr.le, hr.2⟩
    linarith

lemma z_comp {K : ℕ} (Q : Matrix (Fin K) (Fin K) ℝ) (x y : Fin K → ℝ) (j : Fin K) :
    (x + Matrix.vecMul y (1 - Q) : Fin K → ℝ) j = y j - (Matrix.vecMul y Q j - x j) := by
  rw [Matrix.vecMul_sub, Matrix.vecMul_one, Pi.add_apply, Pi.sub_apply]; ring

lemma contOn_w {K : ℕ} (Q : Matrix (Fin K) (Fin K) ℝ) {S : Set ℝ} {x y : ℝ → Fin K → ℝ}
    (hx : ContinuousOn x S) (hy : ContinuousOn y S) (j : Fin K) :
    ContinuousOn (fun s => Matrix.vecMul (y s) Q j - x s j) S :=
  ContinuousOn.sub (f := fun s => Matrix.vecMul (y s) Q j) (g := fun s => x s j)
    (contOn_vecMul hy Q j) (contOn_comp_apply hx j)

lemma monoOn_comp {K : ℕ} {y : ℝ → Fin K → ℝ} {S : Set ℝ} (h : MonotoneOn y S) (j : Fin K) :
    MonotoneOn (fun t => y t j) S := fun _ ha _ hb hab => h ha hb hab j

/-- The key observation (13)–(15), with no hypothesis on `Q`. -/
lemma key_obs_gen {K : ℕ} (Q : Matrix (Fin K) (Fin K) ℝ) (x y z : ℝ → Fin K → ℝ)
    (hx : IsCPlus x) (hy : ContinuousOn y (Set.Ici 0)) (hz : ContinuousOn z (Set.Ici 0)) :
    IsReflectionPair Q x y z ↔
      (InC0 y ∧ (∀ t, 0 ≤ t → y t = piMap Q x y t) ∧
        ∀ t, 0 ≤ t → z t = x t + Matrix.vecMul (y t) (1 - Q)) := by
  constructor
  · rintro ⟨_, _, _, h14, h15, ⟨hmono, h0⟩, h17⟩
    refine ⟨⟨hy, hmono, h0⟩, ?_, h14⟩
    intro t ht
    funext j
    unfold piMap
    refine skor_fwd (fun t => y t j) (fun s => Matrix.vecMul (y s) Q j - x s j)
      (fun t => z t j) (contOn_comp_apply hy j) (contOn_w Q hx.1 hy j) ?_ ?_
      (monoOn_comp hmono j) (by simp [h0]) (h17 j) t ht
    · intro t ht; show z t j = _; rw [h14 t ht, z_comp]
    · intro t ht; exact h15 t ht j
  · rintro ⟨⟨_, hmono, h0⟩, hfix, h14⟩
    have hb : ∀ j, _ := fun j => skor_bwd (fun t => y t j)
      (fun s => Matrix.vecMul (y s) Q j - x s j) (contOn_comp_apply hy j)
      (contOn_w Q hx.1 hy j) (monoOn_comp hmono j) (by simp [h0])
      (fun t ht => by have := congrFun (hfix t ht) j; simpa [piMap] using this)
    refine ⟨hx, hy, hz, h14, ?_, ⟨hmono, h0⟩, ?_⟩
    · intro t ht j
      rw [h14 t ht, z_comp]
      exact (hb j).1 t ht
    · intro j s t hs hst hpos
      apply (hb j).2 s t hs hst
      intro r hr
      have := hpos r hr
      rw [h14 r (hs.trans hr.1), z_comp] at this
      exact this

/-- Weighted Lipschitz estimate for fixed points of `π`. -/
lemma wlip {K : ℕ} (Q : Matrix (Fin K) (Fin K) ℝ) (hQ0 : ∀ i j, 0 ≤ Q i j)
    (v : Fin K → ℝ) (hvpos : ∀ i, 0 < v i) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hv : ∀ j, ∑ i, v i * Q i j ≤ α * v j) (T : ℝ) (hT : 0 ≤ T) (x x' y y' : ℝ → Fin K → ℝ)
    (hx : ContinuousOn x (Set.Icc 0 T)) (hx' : ContinuousOn x' (Set.Icc 0 T))
    (hy : ContinuousOn y (Set.Icc 0 T)) (hy' : ContinuousOn y' (Set.Icc 0 T))
    (hfy : ∀ t ∈ Set.Icc (0 : ℝ) T, y t = piMap Q x y t)
    (hfy' : ∀ t ∈ Set.Icc (0 : ℝ) T, y' t = piMap Q x' y' t)
    (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ j, |x s j - x' s j| ≤ D * v j) :
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i, |y s i - y' s i| ≤ D / (1 - α) * v i := by
  set w : ℝ → Fin K → ℝ := fun s i => (y s i - y' s i) / v i with hw
  have hwc : ContinuousOn (fun s => ‖w s‖) (Set.Icc 0 T) := by
    apply ContinuousOn.norm
    apply continuousOn_pi.2
    intro i
    exact ((contOn_comp_apply hy i).sub (contOn_comp_apply hy' i)).div_const _
  obtain ⟨s0, hs0, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hT) hwc
  set E := ‖w s0‖ with hE
  have hE0 : 0 ≤ E := norm_nonneg _
  have hwi : ∀ s i, |y s i - y' s i| = |w s i| * v i := by
    intro s i
    simp only [hw, abs_div, abs_of_pos (hvpos i)]
    field_simp [(hvpos i).ne']
  have hab : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i, |y s i - y' s i| ≤ E * v i := by
    intro s hs i
    rw [hwi]
    have h1 : |w s i| ≤ ‖w s‖ := by
      have := norm_le_pi_norm (w s) i; rwa [Real.norm_eq_abs] at this
    have h2 : ‖w s‖ ≤ E := hmax hs
    exact mul_le_mul_of_nonneg_right (h1.trans h2) (hvpos i).le
  have core := core_bound Q hQ0 v α hv T x x' y y' hx hx' hy hy' D E hE0 hD hab
  have hEle : E ≤ D + α * E := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro j
    rw [Real.norm_eq_abs]
    have h := core s0 hs0 j
    rw [← hfy s0 hs0, ← hfy' s0 hs0, hwi] at h
    have hvj := hvpos j
    have : |w s0 j| * v j ≤ (D + α * E) * v j := by linarith
    exact le_of_mul_le_mul_right this hvj
  have hE' : E ≤ D / (1 - α) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  intro s hs i
  exact (hab s hs i).trans (mul_le_mul_of_nonneg_right hE' (hvpos i).le)

lemma piMap_contOn {K : ℕ} (Q : Matrix (Fin K) (Fin K) ℝ) {x a : ℝ → Fin K → ℝ}
    (hx : ContinuousOn x (Set.Ici 0)) (ha : ContinuousOn a (Set.Ici 0)) :
    ContinuousOn (piMap Q x a) (Set.Ici 0) := by
  apply continuousOn_pi.2
  intro j
  set h : ℝ → ℝ := fun s => max (Matrix.vecMul (a s) Q j - x s j) 0 with hh
  have hhc : ContinuousOn h (Set.Ici 0) := contOn_inner hx ha Q j
  set g : ℝ → ℝ := fun s => h (max s 0) with hg
  have hgc : Continuous g :=
    hhc.comp_continuous (continuous_id.max continuous_const) (fun s => le_max_right s 0)
  have hF : Continuous fun t : ℝ => sSup ((fun u => g (u * t)) '' Set.Icc 0 1) := by
    apply IsCompact.continuous_sSup (f := fun t u => g (u * t)) isCompact_Icc
    exact hgc.comp (continuous_snd.mul continuous_fst)
  refine hF.continuousOn.congr ?_
  intro t ht
  have ht' : (0:ℝ) ≤ t := ht
  show (⨆ s : Set.Icc (0:ℝ) t, h s) = _
  rw [← sSup_image']
  congr 1
  ext w
  constructor
  · rintro ⟨s, hs, rfl⟩
    rcases eq_or_lt_of_le ht' with h0 | hpos
    · subst h0
      have : s = 0 := le_antisymm hs.2 hs.1
      subst this
      refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      simp [hg]
    · refine ⟨s / t, ⟨div_nonneg hs.1 ht', (div_le_one hpos).2 hs.2⟩, ?_⟩
      simp only [hg]
      rw [div_mul_cancel₀ s hpos.ne', max_eq_left hs.1]
  · rintro ⟨u, hu, rfl⟩
    have h1 : 0 ≤ u * t := mul_nonneg hu.1 ht'
    refine ⟨u * t, ⟨h1, ?_⟩, ?_⟩
    · nlinarith [hu.2]
    · simp only [hg]; rw [max_eq_left h1]

lemma piMap_monoOn {K : ℕ} (Q : Matrix (Fin K) (Fin K) ℝ) {x a : ℝ → Fin K → ℝ}
    (hx : ContinuousOn x (Set.Ici 0)) (ha : ContinuousOn a (Set.Ici 0)) :
    MonotoneOn (piMap Q x a) (Set.Ici 0) := by
  intro t ht t' ht' htt' j
  have ht0 : (0:ℝ) ≤ t := ht
  have : Nonempty (Set.Icc (0 : ℝ) t) := ⟨⟨0, le_rfl, ht0⟩⟩
  have bdd := bdd_of_contOn (T := t')
    (contOn_inner (hx.mono Set.Icc_subset_Ici_self) (ha.mono Set.Icc_subset_Ici_self) Q j) le_rfl
  apply ciSup_le
  rintro ⟨s, hs⟩
  exact le_ciSup bdd (⟨s, hs.1, hs.2.trans htt'⟩ : Set.Icc (0:ℝ) t')

lemma piMap_zero {K : ℕ} (Q : Matrix (Fin K) (Fin K) ℝ) {x a : ℝ → Fin K → ℝ}
    (hx0 : 0 ≤ x 0) (ha0 : a 0 = 0) : piMap Q x a 0 = 0 := by
  funext j
  apply le_antisymm
  · apply ciSup_le
    rintro ⟨s, hs⟩
    have : s = 0 := le_antisymm hs.2 hs.1
    subst this
    simp only [ha0, Matrix.zero_vecMul, Pi.zero_apply]
    have := hx0 j
    simp only [Pi.zero_apply] at this
    apply max_le (by linarith) le_rfl
  · exact Real.iSup_nonneg (fun _ => le_max_right _ _)

lemma exists_wbound {K : ℕ} (v : Fin K → ℝ) (hvpos : ∀ i, 0 < v i) (T : ℝ) (hT : 0 ≤ T)
    (f : ℝ → Fin K → ℝ) (hf : ContinuousOn f (Set.Icc 0 T)) :
    ∃ C, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0:ℝ) T, ∀ i, |f s i| ≤ C * v i := by
  set w : ℝ → Fin K → ℝ := fun s i => f s i / v i with hw
  have hwc : ContinuousOn (fun s => ‖w s‖) (Set.Icc 0 T) := by
    apply ContinuousOn.norm
    apply continuousOn_pi.2
    intro i
    exact (contOn_comp_apply hf i).div_const _
  obtain ⟨s0, hs0, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hT) hwc
  refine ⟨‖w s0‖, norm_nonneg _, ?_⟩
  intro s hs i
  have e : |f s i| = |w s i| * v i := by
    simp only [hw, abs_div, abs_of_pos (hvpos i)]
    field_simp [(hvpos i).ne']
  rw [e]
  have h1 : |w s i| ≤ ‖w s‖ := by
    have := norm_le_pi_norm (w s) i; rwa [Real.norm_eq_abs] at this
  exact mul_le_mul_of_nonneg_right (h1.trans (hmax hs)) (hvpos i).le

lemma le_pi_norm_of_pos {K : ℕ} (v : Fin K → ℝ) (i : Fin K) : v i ≤ ‖v‖ := by
  have := norm_le_pi_norm v i
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans this

lemma contOn_Ici_of_Icc {K : ℕ} {y : ℝ → Fin K → ℝ}
    (h : ∀ T, 0 ≤ T → ContinuousOn y (Set.Icc 0 T)) : ContinuousOn y (Set.Ici 0) := by
  intro t ht
  have ht0 : (0:ℝ) ≤ t := ht
  have h1 := h (t + 1) (by linarith) t ⟨ht0, by linarith⟩
  apply h1.mono_of_mem_nhdsWithin
  rw [← Set.Ici_inter_Iic]
  exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))

/-- Picard iteration: existence, uniqueness and locally uniform convergence (weighted version). -/
theorem picard_gen {K : ℕ} (Q : Matrix (Fin K) (Fin K) ℝ) (hQ0 : ∀ i j, 0 ≤ Q i j)
    (v : Fin K → ℝ) (hvpos : ∀ i, 0 < v i) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hv : ∀ j, ∑ i, v i * Q i j ≤ α * v j) (x : ℝ → Fin K → ℝ) (hx : IsCPlus x) :
    ∃ y : ℝ → Fin K → ℝ, InC0 y ∧ (∀ t, 0 ≤ t → y t = piMap Q x y t) ∧
      (∀ y' : ℝ → Fin K → ℝ, InC0 y' → (∀ t, 0 ≤ t → y' t = piMap Q x y' t) →
        ∀ t, 0 ≤ t → y' t = y t) ∧
      UocTendsto (fun n => picardIter Q x n) y := by
  set Y : ℕ → ℝ → Fin K → ℝ := fun n => picardIter Q x n with hYdef
  have hYs : ∀ n, Y (n + 1) = piMap Q x (Y n) := by
    intro n; simp only [hYdef, picardIter]; rw [Function.iterate_succ_apply']
  have hY0 : Y 0 = 0 := by simp [hYdef, picardIter]
  have hxc : ContinuousOn x (Set.Ici 0) := hx.1
  have hcont : ∀ n, ContinuousOn (Y n) (Set.Ici 0) := by
    intro n; induction n with
    | zero => rw [hY0]; exact continuousOn_const
    | succ n ih => rw [hYs]; exact piMap_contOn Q hxc ih
  have hmono : ∀ n, MonotoneOn (Y n) (Set.Ici 0) := by
    intro n; cases n with
    | zero => rw [hY0]; exact monotoneOn_const
    | succ n => rw [hYs]; exact piMap_monoOn Q hxc (hcont n)
  have hzero : ∀ n, Y n 0 = 0 := by
    intro n; induction n with
    | zero => rw [hY0]; rfl
    | succ n ih => rw [hYs]; exact piMap_zero Q hx.2 ih
  have hsub : ∀ T : ℝ, Set.Icc (0:ℝ) T ⊆ Set.Ici 0 := fun T => Set.Icc_subset_Ici_self
  -- geometric bounds
  have hgeo : ∀ T, 0 ≤ T → ∃ C, 0 ≤ C ∧ ∀ n, ∀ s ∈ Set.Icc (0:ℝ) T, ∀ i,
      |Y (n + 1) s i - Y n s i| ≤ C * α ^ n * v i := by
    intro T hT
    obtain ⟨C, hC0, hC⟩ := exists_wbound v hvpos T hT (Y 1) ((hcont 1).mono (hsub T))
    refine ⟨C, hC0, ?_⟩
    intro n
    induction n with
    | zero =>
      intro s hs i
      rw [hY0]; simpa using hC s hs i
    | succ n ih =>
      intro s hs i
      rw [hYs (n + 1)]
      have := core_bound Q hQ0 v α hv T x x (Y (n + 1)) (Y n) (hxc.mono (hsub T))
        (hxc.mono (hsub T)) ((hcont _).mono (hsub T)) ((hcont _).mono (hsub T)) 0 (C * α ^ n)
        (by positivity) (by intro s _ j; simp) ih s hs i
      rw [← hYs n] at this
      calc _ ≤ 0 * v i + α * (C * α ^ n) * v i := this
        _ = C * α ^ (n + 1) * v i := by ring
  have hvn : ∀ i, v i ≤ ‖v‖ := le_pi_norm_of_pos v
  have hvn0 : 0 ≤ ‖v‖ := norm_nonneg _
  have hdist : ∀ T, 0 ≤ T → ∀ C, 0 ≤ C → (∀ n, ∀ s ∈ Set.Icc (0:ℝ) T, ∀ i,
      |Y (n + 1) s i - Y n s i| ≤ C * α ^ n * v i) →
      ∀ t ∈ Set.Icc (0:ℝ) T, ∀ n, dist (Y n t) (Y (n + 1) t) ≤ (C * ‖v‖) * α ^ n := by
    intro T hT C hC0 hC t ht n
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    rw [Real.norm_eq_abs]
    have e : (Y n t - Y (n + 1) t) i = Y n t i - Y (n + 1) t i := rfl
    rw [e, abs_sub_comm]
    have := hC n t ht i
    have : C * α ^ n * v i ≤ C * α ^ n * ‖v‖ :=
      mul_le_mul_of_nonneg_left (hvn i) (by positivity)
    nlinarith
  have hconv : ∀ t, 0 ≤ t → ∃ a, Tendsto (fun n => Y n t) atTop (𝓝 a) := by
    intro t ht
    obtain ⟨C, hC0, hC⟩ := hgeo t ht
    exact cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric α (C * ‖v‖) hα1
      (hdist t ht C hC0 hC t ⟨ht, le_rfl⟩))
  set y : ℝ → Fin K → ℝ := fun t => limUnder atTop (fun n => Y n t) with hydef
  have hlim : ∀ t, 0 ≤ t → Tendsto (fun n => Y n t) atTop (𝓝 (y t)) :=
    fun t ht => tendsto_nhds_limUnder (hconv t ht)
  -- uniform component bounds
  have hcomp : ∀ T, 0 ≤ T → ∃ C, 0 ≤ C ∧ ∀ n, ∀ t ∈ Set.Icc (0:ℝ) T, ∀ i,
      |Y n t i - y t i| ≤ C * v i * α ^ n / (1 - α) := by
    intro T hT
    obtain ⟨C, hC0, hC⟩ := hgeo T hT
    refine ⟨C, hC0, ?_⟩
    intro n t ht i
    have hl : Tendsto (fun n => Y n t i) atTop (𝓝 (y t i)) :=
      ((continuous_apply i).tendsto _).comp (hlim t ht.1)
    have := dist_le_of_le_geometric_of_tendsto α (C * v i) hα1
      (f := fun n => Y n t i) (fun n => by
        rw [Real.dist_eq, abs_sub_comm]
        calc _ ≤ _ := hC n t ht i
          _ = _ := by ring) hl n
    rwa [Real.dist_eq] at this
  have hunif : ∀ T, 0 ≤ T → ∀ ε, 0 < ε → ∀ᶠ n in atTop, ∀ t ∈ Set.Icc (0:ℝ) T,
      ‖Y n t - y t‖ < ε := by
    intro T hT ε hε
    obtain ⟨C, hC0, hC⟩ := hcomp T hT
    have htend : Tendsto (fun n : ℕ => C * ‖v‖ / (1 - α) * α ^ n) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1).const_mul (C * ‖v‖ / (1 - α))
      simpa using this
    filter_upwards [htend.eventually (gt_mem_nhds hε)] with n hn
    intro t ht
    refine lt_of_le_of_lt ?_ hn
    apply (pi_norm_le_iff_of_nonneg (by
      have : 0 < 1 - α := by linarith
      positivity)).2
    intro i
    rw [Real.norm_eq_abs]
    have h1 := hC n t ht i
    have e : (Y n t - y t) i = Y n t i - y t i := rfl
    rw [e]
    refine h1.trans ?_
    have h1a : 0 < 1 - α := by linarith
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have : C * v i * α ^ n ≤ C * ‖v‖ * α ^ n := by
      have := mul_le_mul_of_nonneg_left (hvn i) hC0
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have hinv : 0 ≤ (1 - α)⁻¹ := inv_nonneg.2 h1a.le
    nlinarith
  have hycT : ∀ T, 0 ≤ T → ContinuousOn y (Set.Icc 0 T) := by
    intro T hT
    have hu : TendstoUniformlyOn Y y atTop (Set.Icc 0 T) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [hunif T hT ε hε] with n hn
      intro t ht
      rw [dist_eq_norm, norm_sub_rev]; exact hn t ht
    exact hu.continuousOn (Eventually.of_forall fun n => (hcont n).mono (hsub T)).frequently
  have hyc : ContinuousOn y (Set.Ici 0) := contOn_Ici_of_Icc hycT
  have hymono : MonotoneOn y (Set.Ici 0) := by
    intro t ht t' ht' htt'
    exact le_of_tendsto_of_tendsto' (hlim t ht) (hlim t' ht') (fun n => hmono n ht ht' htt')
  have hy0 : y 0 = 0 := by
    have h1 := hlim 0 le_rfl
    have h2 : Tendsto (fun n => Y n 0) atTop (𝓝 0) := by simp [hzero]
    exact tendsto_nhds_unique h1 h2
  have hfix : ∀ t, 0 ≤ t → y t = piMap Q x y t := by
    intro t ht
    obtain ⟨C, hC0, hC⟩ := hcomp t ht
    have h1a : 0 < 1 - α := by linarith
    funext j
    have hb : ∀ n, |piMap Q x y t j - y t j| ≤
        (α * C * v j / (1 - α) + C * v j * α / (1 - α)) * α ^ n := by
      intro n
      have hcb := core_bound Q hQ0 v α hv t x x y (Y n) (hxc.mono (hsub t))
        (hxc.mono (hsub t)) (hycT t ht) ((hcont n).mono (hsub t)) 0
        (C * α ^ n / (1 - α)) (by positivity) (by intro s _ j; simp)
        (fun s hs i => by
          rw [abs_sub_comm]
          have := hC n s hs i
          calc _ ≤ C * v i * α ^ n / (1 - α) := this
            _ = C * α ^ n / (1 - α) * v i := by ring) t ⟨ht, le_rfl⟩ j
      rw [← hYs n] at hcb
      have h2 := hC (n + 1) t ⟨ht, le_rfl⟩ j
      calc |piMap Q x y t j - y t j|
          ≤ |piMap Q x y t j - Y (n + 1) t j| + |Y (n + 1) t j - y t j| := abs_sub_le _ _ _
        _ ≤ (0 * v j + α * (C * α ^ n / (1 - α)) * v j) + C * v j * α ^ (n + 1) / (1 - α) :=
            add_le_add hcb h2
        _ = _ := by rw [pow_succ]; ring
    have htend : Tendsto (fun n : ℕ =>
        (α * C * v j / (1 - α) + C * v j * α / (1 - α)) * α ^ n) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1).const_mul
        (α * C * v j / (1 - α) + C * v j * α / (1 - α))
      simpa using this
    have : |piMap Q x y t j - y t j| ≤ 0 := ge_of_tendsto' htend hb
    have := abs_nonpos_iff.1 this
    linarith
  refine ⟨y, ⟨hyc, hymono, hy0⟩, hfix, ?_, ?_⟩
  · intro y' hy' hfix' t ht
    have L := wlip Q hQ0 v hvpos α hα0 hα1 hv t ht x x y' y (hxc.mono (hsub t))
      (hxc.mono (hsub t)) (hy'.1.mono (hsub t)) (hycT t ht) (fun s hs => hfix' s hs.1)
      (fun s hs => hfix s hs.1) 0 le_rfl (by intro s _ j; simp)
    funext i
    have := L t ⟨ht, le_rfl⟩ i
    simp only [zero_div, zero_mul] at this
    have := abs_nonpos_iff.1 this
    linarith
  · intro T ε hε
    by_cases hT : 0 ≤ T
    · exact hunif T hT ε hε
    · exact Eventually.of_forall fun n t ht => absurd (ht.1.trans ht.2) hT

lemma matpow_nonneg {K : ℕ} (P : Matrix (Fin K) (Fin K) ℝ) (hP0 : ∀ i j, 0 ≤ P i j) :
    ∀ k i j, 0 ≤ (P ^ k) i j := by
  intro k
  induction k with
  | zero => intro i j; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (ih i l) (hP0 l j))

/-- A Veinott-type weight vector for a nonnegative matrix with `Pᵐ → 0`. -/
lemma exists_weight {K : ℕ} (P : Matrix (Fin K) (Fin K) ℝ) (hP0 : ∀ i j, 0 ≤ P i j)
    (hP : Tendsto (fun m : ℕ => P ^ m) atTop (𝓝 0)) :
    ∃ v : Fin K → ℝ, (∀ i, 1 ≤ v i) ∧ ∃ α : ℝ, 0 ≤ α ∧ α < 1 ∧
      ∀ j, ∑ i, v i * P i j ≤ α * v j := by
  set u : Fin K → ℝ := fun _ => 1 with hu
  have hc : ∀ j, Tendsto (fun m : ℕ => Matrix.vecMul u (P ^ m) j) atTop (𝓝 0) := by
    intro j
    have : ∀ i, Tendsto (fun m : ℕ => (P ^ m) i j) atTop (𝓝 0) := by
      intro i
      have h1 := tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hP i) j
      simpa using h1
    have h2 := tendsto_finsetSum (Finset.univ : Finset (Fin K)) (fun i _ => this i)
    simp only [Finset.sum_const_zero] at h2
    simpa [vecMul_apply', hu] using h2
  have hev : ∀ᶠ m in atTop, ∀ j, Matrix.vecMul u (P ^ m) j < 1 :=
    Filter.eventually_all.2 (fun j => (hc j).eventually (gt_mem_nhds one_pos))
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hev
  set N := N0 + 1 with hN
  have hcN := hN0 N (by omega)
  set v : Fin K → ℝ := ∑ k ∈ Finset.range N, Matrix.vecMul u (P ^ k) with hv
  have hterm : ∀ k j, 0 ≤ Matrix.vecMul u (P ^ k) j := by
    intro k j
    rw [vecMul_apply']
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (by simp [hu]) (matpow_nonneg P hP0 k i j))
  have hv1 : ∀ j, 1 ≤ v j := by
    intro j
    rw [hv, Finset.sum_apply]
    have h0 : Matrix.vecMul u (P ^ 0) j = 1 := by simp [hu]
    calc (1:ℝ) = Matrix.vecMul u (P ^ 0) j := h0.symm
      _ ≤ ∑ k ∈ Finset.range N, Matrix.vecMul u (P ^ k) j :=
        Finset.single_le_sum (f := fun k => Matrix.vecMul u (P ^ k) j)
          (fun k _ => hterm k j) (Finset.mem_range.2 (by omega))
  have hvP : ∀ j, ∑ i, v i * P i j = v j - 1 + Matrix.vecMul u (P ^ N) j := by
    intro j
    rw [← vecMul_apply', hv, Matrix.sum_vecMul]
    have e : ∀ k, Matrix.vecMul (Matrix.vecMul u (P ^ k)) P = Matrix.vecMul u (P ^ (k + 1)) := by
      intro k; rw [Matrix.vecMul_vecMul, pow_succ]
    simp_rw [e]
    have h1 := Finset.sum_range_succ' (fun k => Matrix.vecMul u (P ^ k)) N
    have h2 := Finset.sum_range_succ (fun k => Matrix.vecMul u (P ^ k)) N
    have h3 : (∑ k ∈ Finset.range N, Matrix.vecMul u (P ^ (k + 1))) =
        (∑ k ∈ Finset.range N, Matrix.vecMul u (P ^ k)) + Matrix.vecMul u (P ^ N)
          - Matrix.vecMul u (P ^ 0) := by
      rw [← h2, h1]; abel
    rw [h3]
    simp [hu]
    ring
  set r : Fin K → ℝ := fun j => (v j - 1 + Matrix.vecMul u (P ^ N) j) / v j with hr
  have hr1 : ∀ j, r j < 1 := by
    intro j
    have := hv1 j
    rw [hr, div_lt_one (by linarith)]
    linarith [hcN j]
  have hrv : ∀ j, ∑ i, v i * P i j = r j * v j := by
    intro j
    rw [hvP j, hr]
    field_simp [(show (0:ℝ) < v j by linarith [hv1 j]).ne']
  refine ⟨v, hv1, ?_⟩
  rcases isEmpty_or_nonempty (Fin K) with hK | hK
  · exact ⟨0, le_rfl, one_pos, fun j => isEmptyElim j⟩
  · obtain ⟨j0, hj0⟩ := exists_eq_ciSup_of_finite (f := r)
    refine ⟨max 0 (⨆ j, r j), le_max_left _ _, ?_, ?_⟩
    · rw [← hj0]; exact max_lt one_pos (hr1 j0)
    · intro j
      rw [hrv j]
      apply mul_le_mul_of_nonneg_right _ (by linarith [hv1 j])
      exact le_trans (le_ciSup (Set.finite_range r).bddAbove j) (le_max_right _ _)

lemma contOn_zpath {K : ℕ} {S : Set ℝ} {x y : ℝ → Fin K → ℝ} (hx : ContinuousOn x S)
    (hy : ContinuousOn y S) (M : Matrix (Fin K) (Fin K) ℝ) :
    ContinuousOn (fun t => x t + Matrix.vecMul (y t) M) S := by
  apply continuousOn_pi.2
  intro j
  exact (contOn_comp_apply hx j).add (contOn_vecMul hy M j)

lemma norm_vecMul_le {K : ℕ} (M : Matrix (Fin K) (Fin K) ℝ) (w : Fin K → ℝ) :
    ‖Matrix.vecMul w M‖ ≤ (∑ i, ∑ j, |M i j|) * ‖w‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro j
  rw [Real.norm_eq_abs, vecMul_apply']
  calc |∑ i, w i * M i j| ≤ ∑ i, |w i * M i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖w‖ * |M i j| := by
        apply Finset.sum_le_sum; intro i _
        rw [abs_mul]
        have := norm_le_pi_norm w i
        rw [Real.norm_eq_abs] at this
        exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    _ = ‖w‖ * ∑ i, |M i j| := by rw [Finset.mul_sum]
    _ ≤ ‖w‖ * ∑ i, ∑ j, |M i j| := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply Finset.sum_le_sum; intro i _
        exact Finset.single_le_sum (f := fun j => |M i j|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ j)
    _ = _ := by ring

lemma uoc_zpath {K : ℕ} (M : Matrix (Fin K) (Fin K) ℝ) (xs ys zs : ℕ → ℝ → Fin K → ℝ)
    (x y z : ℝ → Fin K → ℝ) (hzs : ∀ n t, 0 ≤ t → zs n t = xs n t + Matrix.vecMul (ys n t) M)
    (hz : ∀ t, 0 ≤ t → z t = x t + Matrix.vecMul (y t) M)
    (hx : UocTendsto xs x) (hy : UocTendsto ys y) : UocTendsto zs z := by
  intro T ε hε
  set L := ∑ i, ∑ j, |M i j| with hL
  have hL0 : 0 ≤ L := by positivity
  filter_upwards [hx T (ε / 2) (by linarith), hy T (ε / (2 * (L + 1))) (by positivity)]
    with n hn1 hn2
  intro t ht
  rw [hzs n t ht.1, hz t ht.1]
  have e : xs n t + Matrix.vecMul (ys n t) M - (x t + Matrix.vecMul (y t) M) =
      (xs n t - x t) + Matrix.vecMul (ys n t - y t) M := by
    rw [Matrix.sub_vecMul]; abel
  rw [e]
  have h1 := hn1 t ht
  have h2 := hn2 t ht
  have h3 := norm_vecMul_le M (ys n t - y t)
  calc ‖(xs n t - x t) + Matrix.vecMul (ys n t - y t) M‖
      ≤ ‖xs n t - x t‖ + ‖Matrix.vecMul (ys n t - y t) M‖ := norm_add_le _ _
    _ ≤ ‖xs n t - x t‖ + L * ‖ys n t - y t‖ := by linarith
    _ < ε / 2 + L * (ε / (2 * (L + 1))) := by
        have := mul_le_mul_of_nonneg_left h2.le hL0
        linarith
    _ ≤ ε := by
        have : L * (ε / (2 * (L + 1))) ≤ ε / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        linarith

/-- Reiman's Lemma 1 / Harrison–Reiman Theorem 1 for a general nonnegative `P` with `Pᵐ → 0`. -/
theorem lemma_1_gen {K : ℕ} (P : Matrix (Fin K) (Fin K) ℝ) (hP0 : ∀ i j, 0 ≤ P i j)
    (hP : Tendsto (fun m : ℕ => P ^ m) atTop (𝓝 0)) :
    (∀ x : ℝ → Fin K → ℝ, IsCPlus x →
      ∃ y z, IsReflectionPair P x y z ∧
        ∀ y' z', IsReflectionPair P x y' z' → ∀ t, 0 ≤ t → y' t = y t ∧ z' t = z t) ∧
    (∀ (T : ℝ) (x y z x' y' z' : ℝ → Fin K → ℝ), IsReflectionPair P x y z →
      IsReflectionPair P x' y' z' → (∀ t ∈ Set.Icc (0 : ℝ) T, x t = x' t) →
      ∀ t ∈ Set.Icc (0 : ℝ) T, y t = y' t ∧ z t = z' t) ∧
    (∀ (xs ys zs : ℕ → ℝ → Fin K → ℝ) (x y z : ℝ → Fin K → ℝ),
      (∀ n, IsReflectionPair P (xs n) (ys n) (zs n)) → IsReflectionPair P x y z →
      UocTendsto xs x → UocTendsto ys y ∧ UocTendsto zs z) := by
  obtain ⟨v, hv1, α, hα0, hα1, hv⟩ := exists_weight P hP0 hP
  have hvpos : ∀ i, 0 < v i := fun i => lt_of_lt_of_le one_pos (hv1 i)
  have hsub : ∀ T : ℝ, Set.Icc (0:ℝ) T ⊆ Set.Ici 0 := fun T => Set.Icc_subset_Ici_self
  have fx : ∀ {x y z : ℝ → Fin K → ℝ}, IsReflectionPair P x y z →
      InC0 y ∧ (∀ t, 0 ≤ t → y t = piMap P x y t) ∧
        ∀ t, 0 ≤ t → z t = x t + Matrix.vecMul (y t) (1 - P) :=
    fun h => (key_obs_gen P _ _ _ h.1 h.2.1 h.2.2.1).1 h
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hyC, hyfix, hyuniq, -⟩ := picard_gen P hP0 v hvpos α hα0 hα1 hv x hx
    set z : ℝ → Fin K → ℝ := fun t => x t + Matrix.vecMul (y t) (1 - P) with hz
    have hzc : ContinuousOn z (Set.Ici 0) := contOn_zpath hx.1 hyC.1 (1 - P)
    refine ⟨y, z, (key_obs_gen P x y z hx hyC.1 hzc).2 ⟨hyC, hyfix, fun t _ => rfl⟩, ?_⟩
    intro y' z' h' t ht
    obtain ⟨hC', hfix', hz'⟩ := fx h'
    have := hyuniq y' hC' hfix' t ht
    refine ⟨this, ?_⟩
    rw [hz' t ht, this]
  · intro T x y z x' y' z' h h' hxx t ht
    have hT : 0 ≤ T := ht.1.trans ht.2
    obtain ⟨hC, hfix, hz⟩ := fx h
    obtain ⟨hC', hfix', hz'⟩ := fx h'
    have L := wlip P hP0 v hvpos α hα0 hα1 hv T hT x x' y y' (h.1.1.mono (hsub T))
      (h'.1.1.mono (hsub T)) (hC.1.mono (hsub T)) (hC'.1.mono (hsub T))
      (fun s hs => hfix s hs.1) (fun s hs => hfix' s hs.1) 0 le_rfl
      (by intro s hs j; rw [hxx s hs]; simp)
    have hyy : y t = y' t := by
      funext i
      have := L t ht i
      simp only [zero_div, zero_mul] at this
      have := abs_nonpos_iff.1 this
      linarith
    refine ⟨hyy, ?_⟩
    rw [hz t ht.1, hz' t ht.1, hyy, hxx t ht]
  · intro xs ys zs x y z hs h hxs
    obtain ⟨hC, hfix, hz⟩ := fx h
    have hys : UocTendsto ys y := by
      intro T ε hε
      by_cases hT : 0 ≤ T
      · have h1a : 0 < 1 - α := by linarith
        set δ := ε * (1 - α) / (2 * (‖v‖ + 1)) with hδ
        have hδ0 : 0 < δ := by positivity
        filter_upwards [hxs T δ hδ0] with n hn
        intro t ht
        obtain ⟨hCn, hfixn, -⟩ := fx (hs n)
        have L := wlip P hP0 v hvpos α hα0 hα1 hv T hT (xs n) x (ys n) y
          ((hs n).1.1.mono (hsub T)) (h.1.1.mono (hsub T)) (hCn.1.mono (hsub T))
          (hC.1.mono (hsub T)) (fun s hs => hfixn s hs.1) (fun s hs => hfix s hs.1) δ hδ0.le
          (by
            intro s hs j
            have h1 := norm_le_pi_norm (xs n s - x s) j
            have e : ‖(xs n s - x s) j‖ = |xs n s j - x s j| := by rw [Real.norm_eq_abs]; rfl
            rw [e] at h1
            have := hn s hs
            have := hv1 j
            nlinarith)
        apply (pi_norm_lt_iff hε).2
        intro i
        have e : ‖(ys n t - y t) i‖ = |ys n t i - y t i| := by rw [Real.norm_eq_abs]; rfl
        rw [e]
        refine lt_of_le_of_lt (L t ht i) ?_
        have hvi := le_pi_norm_of_pos v i
        have hvn := norm_nonneg v
        have : δ / (1 - α) = ε / (2 * (‖v‖ + 1)) := by
          rw [hδ]; field_simp
        rw [this]
        have : ε / (2 * (‖v‖ + 1)) * v i ≤ ε / (2 * (‖v‖ + 1)) * ‖v‖ :=
          mul_le_mul_of_nonneg_left hvi (by positivity)
        have : ε / (2 * (‖v‖ + 1)) * ‖v‖ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
        linarith
      · exact Eventually.of_forall fun n t ht => absurd (ht.1.trans ht.2) hT
    refine ⟨hys, ?_⟩
    exact uoc_zpath (1 - P) xs ys zs x y z (fun n t ht => (fx (hs n)).2.2 t ht) hz hxs hys

end RBMOCore

open Reiman84.QueueLength Filter Topology

theorem solution {K : ℕ} (P : Matrix (Fin K) (Fin K) ℝ) (hP0 : ∀ i j, 0 ≤ P i j)
    (hP : Tendsto (fun m : ℕ => P ^ m) atTop (𝓝 0)) :
    (∀ x : ℝ → Fin K → ℝ, IsCPlus x →
      ∃ y z, IsReflectionPair P x y z ∧
        ∀ y' z', IsReflectionPair P x y' z' → ∀ t, 0 ≤ t → y' t = y t ∧ z' t = z t) ∧
    (∀ (T : ℝ) (x y z x' y' z' : ℝ → Fin K → ℝ), IsReflectionPair P x y z →
      IsReflectionPair P x' y' z' → (∀ t ∈ Set.Icc (0 : ℝ) T, x t = x' t) →
      ∀ t ∈ Set.Icc (0 : ℝ) T, y t = y' t ∧ z t = z' t) ∧
    (∀ (xs ys zs : ℕ → ℝ → Fin K → ℝ) (x y z : ℝ → Fin K → ℝ),
      (∀ n, IsReflectionPair P (xs n) (ys n) (zs n)) → IsReflectionPair P x y z →
      UocTendsto xs x → UocTendsto ys y ∧ UocTendsto zs z) :=
  RBMOCore.lemma_1_gen P hP0 hP
