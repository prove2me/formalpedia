-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P23.strong_operator_product_rule
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:12:47.600992+00:00
-- url     : https://prove2.me/submissions/620fadd2-9af1-4f3c-897b-4b2b67d841d8

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P23
noncomputable section

open MeasureTheory

open scoped Interval Classical

open QAlgorithms.Papers.Independent.Claimed50.P23

open Filter Topology Asymptotics

theorem g67f2_left (I : Set ℝ) (t : ℝ) (ht : t ∈ I) :
    ∃ a ∈ I, a ≤ t ∧ ∀ᶠ s in 𝓝[I] t, a ≤ s := by
  by_cases h : ∃ a ∈ I, a < t
  · obtain ⟨a, haI, hat⟩ := h
    exact ⟨a, haI, hat.le, nhdsWithin_le_nhds (Filter.mem_of_superset (Ioi_mem_nhds hat) fun s (hs : a < s) => hs.le)⟩
  · push_neg at h
    exact ⟨t, ht, le_rfl, eventually_nhdsWithin_of_forall fun s hs => h s hs⟩

theorem g67f2_right (I : Set ℝ) (t : ℝ) (ht : t ∈ I) :
    ∃ b ∈ I, t ≤ b ∧ ∀ᶠ s in 𝓝[I] t, s ≤ b := by
  by_cases h : ∃ b ∈ I, t < b
  · obtain ⟨b, hbI, htb⟩ := h
    exact ⟨b, hbI, htb.le, nhdsWithin_le_nhds (Filter.mem_of_superset (Iio_mem_nhds htb) fun s (hs : s < b) => hs.le)⟩
  · push_neg at h
    exact ⟨t, ht, le_rfl, eventually_nhdsWithin_of_forall fun s hs => h s hs⟩

/-- Lemma 4, PDF p.3: the strong-operator product rule. -/
theorem solution
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (D : Submodule ℝ E) (I : Set ℝ) (hI : Set.OrdConnected I)
    (K : ℝ → E →L[ℝ] F)
    (hK : ∀ v : E, ContinuousOn (fun t => K t v) I)
    (hKd : ∀ v : D, ∀ t ∈ I, DifferentiableWithinAt ℝ (fun s => K s (v : E)) I t)
    (gamma gammaVelocity : ℝ → E)
    (hgammaDomain : ∀ t ∈ I, gamma t ∈ D)
    (hgamma : ∀ t ∈ I, HasDerivWithinAt gamma (gammaVelocity t) I t) :
    ∀ t ∈ I, UniqueDiffWithinAt ℝ I t →
      HasDerivWithinAt (fun s => K s (gamma s))
        (derivWithin (fun s => K s (gamma t)) I t + K t (gammaVelocity t)) I t := by
  intro t ht _
  obtain ⟨a, haI, hat, ha⟩ := g67f2_left I t ht
  obtain ⟨b, hbI, htb, hb⟩ := g67f2_right I t ht
  have hJ : Set.Icc a b ⊆ I := hI.out haI hbI
  -- uniform bound on Icc a b
  obtain ⟨C, hC⟩ : ∃ C, ∀ s : Set.Icc a b, ‖K s‖ ≤ C := by
    apply banach_steinhaus
    intro x
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn ((hK x).mono hJ)
    exact ⟨C, fun s => hC s s.property⟩
  have hev : ∀ᶠ s in 𝓝[I] t, s ∈ Set.Icc a b := ha.and hb
  set g' := gammaVelocity t
  set k' := derivWithin (fun s => K s (gamma t)) I t
  have h1 : HasDerivWithinAt (fun s => K s (gamma t)) k' I t :=
    (hKd ⟨gamma t, hgammaDomain t ht⟩ t ht).hasDerivWithinAt
  rw [hasDerivWithinAt_iff_isLittleO] at h1 ⊢
  have h2 := (hasDerivWithinAt_iff_isLittleO.mp (hgamma t ht))
  have h3 : (fun s => K s (gamma s - gamma t - (s - t) • g')) =o[𝓝[I] t] fun s => s - t := by
    refine IsBigO.trans_isLittleO ?_ h2
    refine IsBigO.of_bound C ?_
    filter_upwards [hev] with s hs
    exact (K s).le_of_opNorm_le (hC ⟨s, hs⟩) _
  have h4 : (fun s => (s - t) • (K s g' - K t g')) =o[𝓝[I] t] fun s => s - t := by
    have hc : Tendsto (fun s => K s g' - K t g') (𝓝[I] t) (𝓝 0) := by
      have := (hK g' t ht).tendsto
      simpa using this.sub_const (K t g')
    have := (isBigO_refl (fun s : ℝ => s - t) (𝓝[I] t)).smul_isLittleO
      ((isLittleO_one_iff ℝ).mpr hc)
    simpa using this
  refine ((h1.add h3).add h4).congr_left fun s => ?_
  simp only [map_sub, map_smul, smul_sub, smul_add]
  abel
