-- Prove2me | solution 1 for RhoArbitrage.proposition_C_2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T02:57:52.463788+00:00
-- url     : https://prove2.me/submissions/4096951f-4a0c-419f-971e-6feb6fde1e50

import Mathlib

open Filter Topology

theorem solution {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    (f : ℕ → K → EReal) (F : K → EReal) (hlsc : ∀ t, LowerSemicontinuous (f t))
    (hmono : ∀ x, Monotone (fun t => f t x))
    (hlim : ∀ x, Tendsto (fun t => f t x) atTop (𝓝 (F x))) :
    (∀ t, ∃ x, IsMinOn (f t) Set.univ x) ∧
    (∃ x, IsMinOn F Set.univ x) ∧
    Tendsto (fun t => ⨅ x, f t x) atTop (𝓝 (⨅ x, F x)) ∧
    ∀ xs : ℕ → K, (∀ t, IsMinOn (f t) Set.univ (xs t)) →
      ∀ y, MapClusterPt y atTop xs → IsMinOn F Set.univ y := by
  -- Step 1: each `f t` attains its minimum on the compact nonempty `K`
  have hmin_f : ∀ t, ∃ x, IsMinOn (f t) Set.univ x := by
    intro t
    obtain ⟨a, _, ha⟩ := LowerSemicontinuousOn.exists_isMinOn
      (s := (Set.univ : Set K)) Set.univ_nonempty isCompact_univ
      ((hlsc t).lowerSemicontinuousOn Set.univ)
    exact ⟨a, ha⟩
  let x : ℕ → K := fun t => Classical.choose (hmin_f t)
  have hx : ∀ t, IsMinOn (f t) Set.univ (x t) := fun t => Classical.choose_spec (hmin_f t)
  -- Step 2: `F` is the pointwise supremum of the monotone sequence
  have hF_eq : ∀ z, F z = ⨆ t, f t z := by
    intro z
    apply le_antisymm
    · refine le_of_tendsto (hlim z) (Eventually.of_forall fun t => ?_)
      exact le_iSup (fun t => f t z) t
    · refine iSup_le fun s => ?_
      refine ge_of_tendsto (hlim z) ?_
      exact eventually_atTop.mpr ⟨s, fun t ht => hmono z ht⟩
  -- Step 3: `F` is lower semicontinuous and attains its minimum
  have hlscF : LowerSemicontinuous F := by
    rw [show F = fun z => ⨆ t, f t z from funext hF_eq]
    exact lowerSemicontinuous_iSup hlsc
  have hmin_F : ∃ z, IsMinOn F Set.univ z := by
    obtain ⟨a, _, ha⟩ := LowerSemicontinuousOn.exists_isMinOn
      (s := (Set.univ : Set K)) Set.univ_nonempty isCompact_univ
      (hlscF.lowerSemicontinuousOn Set.univ)
    exact ⟨a, ha⟩
  -- notation for the running minima
  let m : ℕ → EReal := fun t => ⨅ z, f t z
  have hmono_m : Monotone m := by
    intro s t hst
    exact iInf_mono fun z => hmono z hst
  -- `m` is bounded above by the infimum of `F`
  have hm_le : ∀ t, m t ≤ ⨅ z, F z := by
    intro t
    refine le_iInf fun z => ?_
    exact (iInf_le (fun z => f t z) z).trans
      ((le_iSup (fun s => f s z) t).trans (le_of_eq (hF_eq z).symm))
  have hbdd : BddAbove (Set.range m) := by
    refine ⟨⨅ z, F z, ?_⟩
    rintro b ⟨t, rfl⟩
    exact hm_le t
  have htend_m : Tendsto m atTop (𝓝 (⨆ t, m t)) := tendsto_atTop_ciSup hmono_m hbdd
  -- any cluster point of a sequence of minimisers bounds `F` by the limit of the `m t`
  have hcluster_le : ∀ (u : ℕ → K), (∀ t, IsMinOn (f t) Set.univ (u t)) →
      ∀ y, MapClusterPt y atTop u → F y ≤ ⨆ t, m t := by
    intro u hu y hy
    rw [hF_eq y]
    refine iSup_le fun s => ?_
    by_contra hcon
    push_neg at hcon
    have hev : ∀ᶠ z in 𝓝 y, (⨆ t, m t) < f s z := hlsc s y (⨆ t, m t) hcon
    have hfreq : ∃ᶠ t in atTop, u t ∈ {z : K | (⨆ t, m t) < f s z} :=
      (mapClusterPt_iff_frequently.mp hy) _ hev
    have hev2 : ∀ᶠ t : ℕ in atTop, s ≤ t := eventually_atTop.mpr ⟨s, fun t ht => ht⟩
    obtain ⟨t, htU, hst⟩ := (hfreq.and_eventually hev2).exists
    have h1 : (⨆ t, m t) < f s (u t) := htU
    have h2 : f s (u t) ≤ f t (u t) := hmono (u t) hst
    have h3 : f t (u t) ≤ m t :=
      le_iInf fun z => (isMinOn_iff.mp (hu t)) z (Set.mem_univ z)
    have h4 : m t ≤ ⨆ t, m t := le_iSup m t
    exact absurd (lt_of_lt_of_le (lt_of_lt_of_le h1 h2) (h3.trans h4)) (lt_irrefl _)
  -- compactness gives a cluster point
  have hx_cluster : ∃ y, MapClusterPt y atTop x :=
    exists_clusterPt_of_compactSpace (map x atTop)
  have hsup_eq : (⨆ t, m t) = ⨅ z, F z := by
    apply le_antisymm
    · exact iSup_le hm_le
    · obtain ⟨y, hy⟩ := hx_cluster
      exact (iInf_le (fun z => F z) y).trans (hcluster_le x hx y hy)
  refine ⟨hmin_f, hmin_F, ?_, ?_⟩
  · show Tendsto m atTop (𝓝 (⨅ z, F z))
    rw [← hsup_eq]
    exact htend_m
  · intro xs hxs y hy
    rw [isMinOn_iff]
    intro z _
    calc F y ≤ ⨆ t, m t := hcluster_le xs hxs y hy
      _ = ⨅ z, F z := hsup_eq
      _ ≤ F z := iInf_le (fun z => F z) z
