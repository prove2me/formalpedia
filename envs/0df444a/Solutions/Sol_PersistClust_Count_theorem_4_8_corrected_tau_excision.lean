-- Prove2me | solution 1 for PersistClust.Count.theorem_4_8_corrected_tau_excision
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T17:24:38.894407+00:00
-- url     : https://prove2.me/submissions/31a3ba97-7d5e-497c-8bd4-177a720675df

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips

open PersistClust.Count

/-- Tau-excision: if no sample value equals τ > 0, the Rips persistence diagram
of a finite sample vanishes at every point born at τ whose death coordinate is at
most 0 (including the essential case, death = bottom). Rips births are vertex
values, and the finite sample has a positive gap to τ, so the two stage sets at
τ − ε and τ + ε coincide for small ε; every rank difference in the diagram's
infimum formula collapses. -/
theorem solution {X : Type*} [MetricSpace X] {n : ℕ} (f : X → ℝ) (τ : ℝ) (δ : ℝ)
    (pts : Fin n → X) (hτ : 0 < τ) (hne : ∀ i : Fin n, f (pts i) ≠ τ)
    (d : EReal) (hd : d ≤ ((0 : ℝ) : EReal)) :
    ripsDiagram (fun i j => dist (pts i) (pts j)) (f ∘ pts) δ (((τ : ℝ) : EReal), d) = 0 := by
  -- PLAN: ripsDiagram Dm (f o pts) delta (coe tau, d) unfolds to
  -- mult (ripsRank Dm (f o pts) delta) (coe tau, d). Outer ifs: coe tau != bot / != top
  -- (EReal.coe_ne_bot, EReal.coe_ne_top); p.1.toReal = tau (EReal.toReal_coe).
  -- CASES on d : EReal (bot / coe d' / top); top excluded by hd via EReal.coe_lt_top;
  -- coe d': d' <= 0 (coe_le_coe) so p.2 < p.1 by coe_lt_coe (d' <= 0 < htau).
  --   bot d  : M = INF eps 0<eps, INF t (t <= tau-eps), r (tau-eps) t - r (tau+eps) t.
  --   coe d' : 4-term INF over eps in Set.Ioo 0 ((tau - d')/2).
  -- GAP: S := image (fun i => |f (pts i) - tau|) univ. Empty (n = 0): stage sets are all
  -- empty so the two levels agree for any eps. Nonempty: gamma := S.min' > 0 (elements
  -- positive by hne) and gamma <= |f (pts i) - tau| for all i (Finset.min'_le).
  -- STAGE-CONSTANCY: pick eps0 with 0 < eps0 < gamma (also eps0 < (tau-d')/2 in coe case);
  -- no g i in [tau-eps0, tau+eps0), so {i | tau-eps0 <= g i} = {i | tau+eps0 <= g i},
  -- hence ripsRank Dm g delta (tau-eps0) = ripsRank Dm g delta (tau+eps0) (rank depends
  -- only on the stage set / joined relation at the level).
  -- BOUNDS: upper by iInf2_le at eps0, differences collapse via tsub_self (twice in the
  -- 4-term branch); lower by zero_le + le_iInf; conclude le_antisymm.
  -- FILL: three-case mult evaluation via EReal.rec on the death coordinate,
  -- per the banked plan above: gap gamma, stage-constancy window, rank agreement, then
  -- le_antisymm (upper: iInf_le_of_le at eps0 where the bracket collapses by tsub_self;
  -- lower: le_iInf with the canonically-ordered ENat zero_le).
  have hgap : ∃ γ : ℝ, 0 < γ ∧ ∀ i : Fin n, γ ≤ |(f ∘ pts) i - τ| := by
    rcases isEmpty_or_nonempty (Fin n) with hempty | hne'
    · haveI : IsEmpty (Fin n) := hempty
      exact ⟨1, one_pos, fun i => isEmptyElim i⟩
    · obtain ⟨i0⟩ := hne'
      have hSne : (Finset.univ.image fun i : Fin n => |(f ∘ pts) i - τ|).Nonempty :=
        ⟨|(f ∘ pts) i0 - τ|, Finset.mem_image_of_mem _ (Finset.mem_univ i0)⟩
      refine ⟨(Finset.univ.image fun i : Fin n => |(f ∘ pts) i - τ|).min' hSne, ?_, fun i => ?_⟩
      · obtain ⟨i1, -, hmem⟩ := Finset.mem_image.mp (Finset.min'_mem _ hSne)
        rw [← hmem]
        exact abs_pos.mpr (sub_ne_zero.mpr (hne i1))
      · exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  obtain ⟨γ, hγpos, hγle⟩ := hgap
  have hsets : ∀ ε : ℝ, 0 < ε → ε < γ →
      {i : Fin n | τ - ε ≤ (f ∘ pts) i} = {i : Fin n | τ + ε ≤ (f ∘ pts) i} := by
    intro ε hεpos hεγ
    ext i
    constructor
    · intro h
      have h' : τ - ε ≤ (f ∘ pts) i := h
      rcases le_or_gt (τ + ε) ((f ∘ pts) i) with hge | hlt
      · exact hge
      · have habs : |(f ∘ pts) i - τ| ≤ ε := abs_le.mpr ⟨by linarith, by linarith⟩
        exact absurd (le_trans (hγle i) habs) (by linarith)
    · intro h
      have h' : τ + ε ≤ (f ∘ pts) i := h
      show τ - ε ≤ (f ∘ pts) i
      linarith
  have hstage : ∀ s1 s2 : ℝ, {i : Fin n | s1 ≤ (f ∘ pts) i} = {i : Fin n | s2 ≤ (f ∘ pts) i} →
      ∀ t : ℝ, ripsRank (fun i j => dist (pts i) (pts j)) (f ∘ pts) δ s1 t
          = ripsRank (fun i j => dist (pts i) (pts j)) (f ∘ pts) δ s2 t := by
    intro s1 s2 hs t
    show ((fun x : Fin n => {y : Fin n | ripsJoined (fun i j => dist (pts i) (pts j))
          (f ∘ pts) δ t x y}) '' {i : Fin n | s1 ≤ (f ∘ pts) i}).encard
        = ((fun x : Fin n => {y : Fin n | ripsJoined (fun i j => dist (pts i) (pts j))
          (f ∘ pts) δ t x y}) '' {i : Fin n | s2 ≤ (f ∘ pts) i}).encard
    rw [hs]
  show mult (ripsRank (fun i j => dist (pts i) (pts j)) (f ∘ pts) δ) (((τ : ℝ) : EReal), d) = 0
  induction d using EReal.rec with
  | bot =>
    unfold mult
    rw [if_pos ⟨EReal.coe_ne_bot τ, EReal.coe_ne_top τ⟩, if_pos rfl]
    simp only [EReal.toReal_coe]
    have hεpos : 0 < γ / 2 := half_pos hγpos
    have hset : {i : Fin n | τ - γ / 2 ≤ (f ∘ pts) i}
        = {i : Fin n | τ + γ / 2 ≤ (f ∘ pts) i} := hsets (γ / 2) hεpos (by linarith)
    refine le_antisymm ?_ (le_iInf fun _ => le_iInf fun _ => le_iInf fun _ =>
      (zero_le : (0 : ℕ∞) ≤ _))
    refine iInf_le_of_le (γ / 2) (iInf_le_of_le hεpos (iInf_le_of_le (τ - γ / 2)
      (iInf_le_of_le (le_refl _) ?_)))
    rw [hstage (τ - γ / 2) (τ + γ / 2) hset (τ - γ / 2), tsub_self]
  | coe d' =>
    have hd'le : d' ≤ 0 := EReal.coe_le_coe_iff.mp hd
    unfold mult
    rw [if_pos ⟨EReal.coe_ne_bot τ, EReal.coe_ne_top τ⟩, if_neg (EReal.coe_ne_bot d'),
        if_pos (EReal.coe_lt_coe_iff.mpr (lt_of_le_of_lt hd'le hτ))]
    simp only [EReal.toReal_coe]
    have hpos : 0 < min (γ / 2) ((τ - d') / 4) :=
      lt_min (half_pos hγpos) (div_pos (by linarith) (by norm_num))
    have hw : min (γ / 2) ((τ - d') / 4) < (τ - d') / 2 :=
      lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hγm : min (γ / 2) ((τ - d') / 4) < γ :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hset : {i : Fin n | τ - min (γ / 2) ((τ - d') / 4) ≤ (f ∘ pts) i}
        = {i : Fin n | τ + min (γ / 2) ((τ - d') / 4) ≤ (f ∘ pts) i} :=
      hsets _ hpos hγm
    refine le_antisymm ?_ (le_iInf fun _ => le_iInf fun _ =>
      (zero_le : (0 : ℕ∞) ≤ _))
    refine iInf_le_of_le (min (γ / 2) ((τ - d') / 4)) (iInf_le_of_le ⟨hpos, hw⟩ ?_)
    rw [hstage _ _ hset (d' + min (γ / 2) ((τ - d') / 4)),
        hstage _ _ hset (d' - min (γ / 2) ((τ - d') / 4)),
        tsub_self, zero_tsub]
  | top =>
    exact absurd hd (not_le.mpr (EReal.coe_lt_top 0))
