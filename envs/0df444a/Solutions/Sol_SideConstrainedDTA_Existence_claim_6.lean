-- Prove2me | solution 1 for SideConstrainedDTA.Existence.claim_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T23:37:41.547984+00:00
-- url     : https://prove2.me/submissions/6d256a08-ed45-4e12-9547-8d36e3529106

import Mathlib
import Definitions.Def_SideConstrainedDTA_Existence_Setting
import Theorems.Thm_SideConstrainedDTA_Existence_claim_5

open MeasureTheory Set Filter Topology

open SideConstrainedDTA.Existence

lemma SideConstrainedDTA.Existence.Sol6.exists_of_ae {a b : ℝ} (J : Set ℝ) (hJI : J ⊆ Icc a b)
    (hJm : MeasurableSet J) (hJpos : 0 < volume J) (P : ℝ → Prop)
    (hP : ∀ᵐ t ∂(volume.restrict (Icc a b)), P t) : ∃ t ∈ J, P t := by
  by_contra hcon
  have hsub : J ⊆ {t | ¬ P t} := fun t ht hPt => hcon ⟨t, ht, hPt⟩
  have h0 := measure_mono_null hsub (ae_iff.1 hP)
  rw [Measure.restrict_apply hJm, inter_eq_left.2 hJI] at h0
  exact (ne_of_gt hJpos) h0

open SideConstrainedDTA.Existence.Sol6 in
theorem solution {I W E : Type*} [Fintype I] [Fintype W] [Fintype E] [DecidableEq I]
    [DecidableEq W] [DecidableEq E] (N : Model I W E) (hN : N.Standing)
    (h2 : A2 N) (h3 : A3 N) (h5 : A5 N) (h9 : A9 N) (h10 : A10 N) (h11 : A11 N) (h12 : A12 N)
    (h13 : A13 N) (h14 : A14 N) (h15 : A15 N) (h16 : A16 N) (h17 : A17 N) (h18 : A18 N)
    (h19 : A19 N)
    (lam : ℕ → ℝ) (hlam : ∀ n, 0 < lam n) (hlam' : Tendsto lam atTop atTop)
    (hs : ℕ → W → ℝ → ℝ) (heq : ∀ n, IsDTCEq N (PsiPen N (lam n)) (hs n))
    (hstar : W → ℝ → ℝ) (hLam : Lam N hstar) (hweak : WeakTendsto N hs hstar) :
    capFeasible N hstar := by
  refine ⟨hLam, fun e θ hθ => ?_⟩
  by_contra hcon
  push Not at hcon
  set D := N.f hstar e θ - N.c e θ with hD
  have hDpos : 0 < D := by linarith
  set L := N.c e θ + D / 2 with hL
  obtain ⟨M, hM0, hM⟩ := claim_5 N hN h2 h10 h18 h19
  have hc : WeakConvSeq N hs hstar := ⟨fun n => (heq n).1, hLam, hweak⟩
  have hT : Tendsto (fun n => N.f (hs n) e θ) atTop (𝓝 (N.f hstar e θ)) :=
    (h14 hs hstar hc e).tendsto_at (show θ ∈ Ici (0:ℝ) from hθ)
  have ev1 : ∀ᶠ n in atTop, L < N.f (hs n) e θ := hT.eventually (lt_mem_nhds (by linarith))
  have ev2 : ∀ᶠ n in atTop, 2 * M / D < lam n := hlam'.eventually_gt_atTop _
  obtain ⟨n, hn1, hn2⟩ := (ev1.and ev2).exists
  have hlamD : M < lam n * (D / 2) := by
    rw [div_lt_iff₀ hDpos] at hn2; nlinarith
  have hLamn := (heq n).1
  set g := N.f (hs n) e with hg
  have hgc : ContinuousOn g (Ici 0) := h13 e (hs n) hLamn
  have hgc' : ContinuousOn g (Icc 0 θ) := hgc.mono Icc_subset_Ici_self
  set K := Icc 0 θ ∩ g ⁻¹' Iic L with hK
  have hKc : IsCompact K :=
    isCompact_Icc.of_isClosed_subset
      (hgc'.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic) inter_subset_left
  have hc0θ : N.c e 0 ≤ N.c e θ := h12 e (show (0:ℝ) ∈ Ici 0 from mem_Ici.2 le_rfl) hθ hθ
  have h0K : (0:ℝ) ∈ K := ⟨⟨le_rfl, hθ⟩, by
    show g 0 ≤ L
    have := h9 e (hs n) hLamn
    linarith⟩
  obtain ⟨a, haK, hamax⟩ := hKc.exists_isGreatest ⟨0, h0K⟩
  have ha0 : 0 ≤ a := haK.1.1
  have haθ : a ≤ θ := haK.1.2
  have hga : g a ≤ L := haK.2
  have hgaL : g a = L := by
    obtain ⟨c', hc'I, hc'⟩ := intermediate_value_Icc haθ (hgc'.mono (Icc_subset_Icc ha0 le_rfl))
      (show L ∈ Icc (g a) (g θ) from ⟨hga, hn1.le⟩)
    have : c' ∈ K := ⟨⟨ha0.trans hc'I.1, hc'I.2⟩, by show g c' ≤ L; rw [hc']⟩
    have hle := hamax this
    have : c' = a := le_antisymm hle hc'I.1
    rw [← this, hc']
  have hge : ∀ ϑ ∈ Icc a θ, L ≤ g ϑ := by
    intro ϑ hϑ
    by_contra hlt
    push Not at hlt
    have : ϑ ∈ K := ⟨⟨ha0.trans hϑ.1, hϑ.2⟩, hlt.le⟩
    have : ϑ = a := le_antisymm (hamax this) hϑ.1
    rw [this, hgaL] at hlt
    exact lt_irrefl _ hlt
  have hcθ0 : 0 ≤ N.c e θ := h11 e θ hθ
  obtain ⟨p, j, hj, hpe, J, hJI, hJm, hJpos, hJ⟩ :=
    h15 (hs n) hLamn e a θ ha0 haθ (show 0 ≤ g a by rw [hgaL]; linarith)
      (show g a < g θ by rw [hgaL]; exact hn1)
  obtain ⟨ν, hν⟩ := (heq n).2 (N.com p)
  obtain ⟨p', hp', J', hJ'I, hJ'm, hJ'pos, hJ'⟩ := hM (lam n) (hlam n).le (N.com p) (hs n) hLamn
  obtain ⟨t', ht'J, ht'⟩ := exists_of_ae J' hJ'I hJ'm hJ'pos _ (hν p' hp')
  have hνM : ν ≤ M := (ht'.2 (hJ' t' ht'J).1).trans (hJ' t' ht'J).2
  obtain ⟨t, htJ, ht⟩ := exists_of_ae J hJI hJm hJpos _ (hν p rfl)
  have hle := ht.1 (hJ t htJ).1
  have htI : t ∈ Icc N.t0 N.tf := hJI htJ
  have hτ := (hJ t htJ).2
  have hPsi0 := (hN.2 (hs n) hLamn p).1 t htI
  have hxi : D / 2 ≤ xiWalk N (hs n) p t := by
    have hterm : D / 2 ≤ xi N (hs n) ((N.edges p)[j]) (N.tau (hs n) p j t) := by
      unfold xi
      rw [hpe]
      refine le_trans ?_ (le_max_right _ _)
      have h1 := hge _ hτ
      have h2 : N.c e (N.tau (hs n) p j t) ≤ N.c e θ :=
        h12 e (show N.tau (hs n) p j t ∈ Ici 0 from ha0.trans hτ.1) hθ hτ.2
      show D / 2 ≤ g (N.tau (hs n) p j t) - N.c e (N.tau (hs n) p j t)
      linarith
    have := Finset.single_le_sum (f := fun k : Fin (N.edges p).length =>
        xi N (hs n) ((N.edges p)[k]) (N.tau (hs n) p k t))
      (fun k _ => le_max_left _ _) (Finset.mem_univ ⟨j, hj⟩)
    exact hterm.trans this
  have hpen : lam n * (D / 2) ≤ PsiPen N (lam n) (hs n) p t := by
    unfold PsiPen
    have := mul_le_mul_of_nonneg_left hxi (hlam n).le
    linarith
  linarith
