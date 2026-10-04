-- Prove2me | solution 1 for TeschlODE.Stability.sublevelComponent_positively_invariant
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:14:15.810166+00:00
-- url     : https://prove2.me/submissions/3c14c88c-253f-4cf2-b9ae-c8f5b67e314c

import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve
import Definitions.Def_TeschlODE_Stability_IsMaximalFlow
import Definitions.Def_TeschlODE_Stability_IsLiapunovFunction
import Definitions.Def_TeschlODE_Stability_semiOrbit
import Definitions.Def_TeschlODE_Stability_sublevelComponent

open TeschlODE.Stability Filter Topology

theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ M) (hfix : f x₀ = 0)
    (U : Set (EuclideanSpace ℝ (Fin n))) (L : EuclideanSpace ℝ (Fin n) → ℝ)
    (hL : IsLiapunovFunction f M x₀ U L) (δ : ℝ)
    (hclosed : IsClosed (sublevelComponent U L x₀ δ)) :
    ∀ x ∈ sublevelComponent U L x₀ δ,
      semiOrbit 1 I Φ x ⊆ sublevelComponent U L x₀ δ := by
  obtain ⟨hUo, hx₀U, hUM, -, -, -, hmono⟩ := hL
  set Fs : Set (EuclideanSpace ℝ (Fin n)) := {x | x ∈ U ∧ L x ≤ δ} with hFs
  set S := sublevelComponent U L x₀ δ with hS
  have hSF : S ⊆ Fs := connectedComponentIn_subset _ _
  -- the fixed point is a stationary solution
  have hconst : Set.univ ⊆ I x₀ ∧ ∀ t, Φ t x₀ = x₀ := by
    have hic : IsIntegralCurve f M Set.univ (fun _ => x₀) :=
      ⟨isOpen_univ, Set.ordConnected_univ, fun _ _ => hx₀, fun t _ => by
        rw [hfix]; exact hasDerivAt_const t x₀⟩
    obtain ⟨h1, h2⟩ := (hΦ x₀ hx₀).2.2.2 Set.univ (fun _ => x₀) hic (Set.mem_univ 0) rfl
    exact ⟨h1, fun t => (h2 t (Set.mem_univ t)).symm⟩
  rintro x hx y ⟨t, ht, htpos, rfl⟩
  have hxF := hSF hx
  have hxM : x ∈ M := hUM hxF.1
  obtain ⟨⟨hIo, hIc, hφM, hφd⟩, h0I, hΦ0, -⟩ := hΦ x hxM
  have hS_eq : S = connectedComponentIn Fs x := connectedComponentIn_eq hx
  by_cases hxx₀ : x = x₀
  · subst hxx₀
    rw [hconst.2 t]
    exact hx
  -- the trajectory never reaches the fixed point
  have hne : ∀ s ∈ I x, Φ s x ≠ x₀ := by
    intro s hs hsx
    set J : Set ℝ := {r | r + s ∈ I x} with hJ
    have hic : IsIntegralCurve f M J (fun r => Φ (r + s) x) := by
      refine ⟨hIo.preimage (continuous_id.add continuous_const), ⟨fun a ha b hb c hc => ?_⟩,
        fun r hr => hφM _ hr, fun r hr => ?_⟩
      · exact hIc.out ha hb ⟨by linarith [hc.1], by linarith [hc.2]⟩
      · exact (hφd _ hr).comp_add_const r s
    obtain ⟨-, h2⟩ := (hΦ x₀ hx₀).2.2.2 J _ hic (by simpa [hJ] using hs) (by simpa using hsx)
    have := h2 (-s) (by simpa [hJ] using h0I)
    simp only [neg_add_cancel, hΦ0, hconst.2] at this
    exact hxx₀ this
  have hcont : ∀ s ∈ I x, ContinuousAt (fun r => Φ r x) s :=
    fun s hs => (hφd s hs).continuousAt
  have hIcc : ∀ s, 0 ≤ s → s ≤ t → s ∈ I x := fun s hs1 hs2 => hIc.out h0I ht ⟨hs1, hs2⟩
  have ht0 : 0 < t := by simpa using htpos
  -- the exit-time argument
  set K : Set ℝ := {s | s ∈ Set.Icc 0 t ∧ (fun r => Φ r x) '' Set.Icc 0 s ⊆ S} with hK
  have hK0 : (0 : ℝ) ∈ K := ⟨⟨le_rfl, ht0.le⟩, by
    rintro _ ⟨r, hr, rfl⟩
    show Φ r x ∈ S; rw [show r = 0 by linarith [hr.1, hr.2], hΦ0]; exact hx⟩
  have hKbdd : BddAbove K := ⟨t, fun s hs => hs.1.2⟩
  set s₀ := sSup K with hs₀
  have hs₀0 : 0 ≤ s₀ := le_csSup hKbdd hK0
  have hs₀t : s₀ ≤ t := csSup_le ⟨0, hK0⟩ fun s hs => hs.1.2
  have hbelow : ∀ r, 0 ≤ r → r < s₀ → Φ r x ∈ S := by
    intro r hr0 hrs
    obtain ⟨s, hsK, hrs'⟩ := exists_lt_of_lt_csSup ⟨0, hK0⟩ hrs
    exact hsK.2 ⟨r, ⟨hr0, hrs'.le⟩, rfl⟩
  have hs₀S : Φ s₀ x ∈ S := by
    rcases hs₀0.lt_or_eq with hpos | hzero
    · have hlim : Tendsto (fun r => Φ r x) (𝓝[<] s₀) (𝓝 (Φ s₀ x)) :=
        (hcont s₀ (hIcc s₀ hs₀0 hs₀t)).tendsto.mono_left nhdsWithin_le_nhds
      apply hclosed.mem_of_tendsto hlim
      filter_upwards [Ioo_mem_nhdsLT hpos] with r hr
      exact hbelow r hr.1.le hr.2
    · rw [← hzero, hΦ0]; exact hx
  have hs₀K : s₀ ∈ K := by
    refine ⟨⟨hs₀0, hs₀t⟩, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    rcases hr.2.lt_or_eq with h | h
    · exact hbelow r hr.1 h
    · rw [h]; exact hs₀S
  have hs₀eq : s₀ = t := by
    by_contra hlt
    have hlt : s₀ < t := lt_of_le_of_ne hs₀t hlt
    have hs₀I := hIcc s₀ hs₀0 hs₀t
    have hS₀U : Φ s₀ x ∈ U := (hSF hs₀S).1
    -- a neighbourhood of `s₀` stays in `U` and in `I x`
    have hev : ∀ᶠ r in 𝓝 s₀, Φ r x ∈ U ∧ r ∈ I x :=
      ((hcont s₀ hs₀I).eventually (hUo.mem_nhds hS₀U)).and (hIo.mem_nhds hs₀I)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    set s' := min t (s₀ + ε / 2) with hs'
    have hs's₀ : s₀ < s' := lt_min hlt (by linarith)
    have hs'K : s' ∈ K := by
      refine ⟨⟨by linarith, min_le_left _ _⟩, ?_⟩
      have hsub : (fun r => Φ r x) '' Set.Icc 0 s' ⊆ Fs := by
        rintro _ ⟨r, hr, rfl⟩
        rcases le_or_gt r s₀ with hrs | hrs
        · exact hSF (hs₀K.2 ⟨r, ⟨hr.1, hrs⟩, rfl⟩)
        · have hrd : dist r s₀ < ε := by
            rw [Real.dist_eq, abs_of_pos (by linarith)]
            have := min_le_right t (s₀ + ε / 2)
            linarith [hr.2]
          obtain ⟨hrU, hrI⟩ := hball hrd
          refine ⟨hrU, ?_⟩
          have := hmono (I x) (fun r => Φ r x) ⟨hIo, hIc, hφM, hφd⟩ s₀ hs₀I r hrI hrs
            ⟨hS₀U, hne s₀ hs₀I⟩ ⟨hrU, hne r hrI⟩
          exact le_trans this (hSF hs₀S).2
      have hpre : IsPreconnected ((fun r => Φ r x) '' Set.Icc 0 s') := by
        apply isPreconnected_Icc.image
        intro r hr
        exact (hcont r (hIcc r hr.1 (le_trans hr.2 (min_le_left _ _)))).continuousWithinAt
      have hx_in : x ∈ (fun r => Φ r x) '' Set.Icc 0 s' := ⟨0, ⟨le_rfl, by linarith⟩, hΦ0⟩
      rw [hS_eq]
      exact hpre.subset_connectedComponentIn hx_in hsub
    have := le_csSup hKbdd hs'K
    linarith
  rw [← hs₀eq]
  exact hs₀S

#print axioms solution
