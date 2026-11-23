-- Prove2me | solution 1 for SteinerNav.corollary_4_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:07:20.467028+00:00
-- url     : https://prove2.me/submissions/023672e7-390e-4272-8998-2cacb0c88883

import Mathlib
import Definitions.Def_SteinerNav_annularCandidates
import Theorems.Thm_SteinerNav_lemma_4_1
import Theorems.Thm_SteinerNav_annuli_cover_targets

open SteinerNav MeasureTheory RegretBandits.Nonlinear

namespace AuxCor42

lemma minDist_pos_of_card {d : ℕ} (P : Finset (Pt d)) (hn : 2 ≤ P.card) :
    0 < minDist P := by
  have h1 : 1 < P.card := by omega
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := Finset.one_lt_card.mp h1
  let offDiag : Finset (Pt d × Pt d) := (P ×ˢ P).filter fun e => e.1 ≠ e.2
  let Dset : Finset ℝ := offDiag.image fun e => dist e.1 e.2
  have hmem₀ : (x₀, y₀) ∈ offDiag :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx₀, hy₀⟩, hxy₀⟩
  have hne : Dset.Nonempty := ⟨dist x₀ y₀, Finset.mem_image.mpr ⟨(x₀, y₀), hmem₀, rfl⟩⟩
  have hset : {r : ℝ | ∃ x ∈ P, ∃ y ∈ P, x ≠ y ∧ r = dist x y} = (Dset : Set ℝ) := by
    ext r
    simp only [Set.mem_setOf, Finset.mem_coe, Dset, offDiag, Finset.mem_image,
      Finset.mem_filter, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨x, hx, y, hy, hne', rfl⟩
      exact ⟨x, y, ⟨⟨hx, hy⟩, hne'⟩, rfl⟩
    · rintro ⟨x, y, ⟨⟨hx, hy⟩, hne'⟩, rfl⟩
      exact ⟨x, hx, y, hy, hne', rfl⟩
  have hmin_eq : minDist P = Dset.min' hne := by
    rw [minDist, hset]
    exact IsLeast.csInf_eq (Finset.isLeast_min' Dset hne)
  obtain ⟨⟨x₁, y₁⟩, hxy₁, hdist₁⟩ := Finset.mem_image.mp (Finset.min'_mem Dset hne)
  rw [hmin_eq, ← hdist₁]
  exact dist_pos.mpr (Finset.mem_filter.mp hxy₁).2

lemma isProb_uniformSphere {d : ℕ} (hd : 1 ≤ d) {P : Finset (Pt d)} (hn : 2 ≤ P.card) :
    IsProbabilityMeasure (uniformSphere d) := by
  obtain ⟨c₀, hc₀, h41⟩ := SteinerNav.lemma_4_1
  obtain ⟨s₀, _, t₀, _, hst₀⟩ := Finset.one_lt_card.mp (show 1 < P.card by omega)
  have hr₀ : 0 < dist s₀ t₀ := dist_pos.mpr hst₀
  have hle2 : dist s₀ t₀ ≤ 2 * dist s₀ t₀ := by linarith
  have hpos_sub : (0 : ENNReal) < uniformSphere d {u : Pt d |
      Covers (1 + 1 / (d : ℝ)) s₀
        (s₀ + (dist s₀ t₀ * Real.sqrt (2 * samplingEps (1 + 1 / (d : ℝ)))) • u) t₀} :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hc₀) (h41 d hd s₀ t₀ (dist s₀ t₀) hst₀ hr₀ le_rfl hle2)
  have hpos_univ : (0 : ENNReal) < uniformSphere d Set.univ :=
    lt_of_lt_of_le hpos_sub (measure_mono (Set.subset_univ _))
  refine ⟨?_⟩
  unfold uniformSphere at hpos_univ ⊢
  simp only [Measure.smul_apply, smul_eq_mul] at hpos_univ ⊢
  have hM_ne_zero : sphereMeasure d Set.univ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hpos_univ
    exact lt_irrefl _ hpos_univ
  have hM_ne_top : sphereMeasure d Set.univ ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.inv_top, zero_mul] at hpos_univ
    exact lt_irrefl _ hpos_univ
  exact ENNReal.inv_mul_cancel hM_ne_zero hM_ne_top

noncomputable def scalePt {d : ℕ} (α : ℝ) (P : Finset (Pt d)) (s : Pt d) (i : ℕ) (w : Pt d) : Pt d :=
  s + ((2 : ℝ) ^ i * minDist P * Real.sqrt (2 * samplingEps α)) • w

def singleFailSet {d : ℕ} (α : ℝ) (P : Finset (Pt d)) (s t : Pt d) (i : ℕ) : Set (Pt d) :=
  {w : Pt d | ¬ Covers α s (scalePt α P s i w) t}

def targetBadSet {d : ℕ} (α : ℝ) (P : Finset (Pt d)) (s t : Pt d) (K L : ℕ) (i : Fin L) :
    Set (Fin L × Fin K → Pt d) :=
  Set.univ.pi fun ij : Fin L × Fin K =>
    if ij.1 = i then singleFailSet α P s t (i : ℕ) else Set.univ

lemma continuous_dist_affine {d : ℕ} (s t : Pt d) (c : ℝ) :
    Continuous (fun w : Pt d => dist (s + c • w) t) := by
  fun_prop

lemma measurableSet_singleFailSet {d : ℕ} (α : ℝ) (P : Finset (Pt d)) (s t : Pt d) (i : ℕ) :
    MeasurableSet (singleFailSet α P s t i) := by
  have heq : singleFailSet α P s t i = {w : Pt d | dist s t / α ≤ dist (scalePt α P s i w) t} := by
    ext w
    simp only [singleFailSet, Covers, Set.mem_setOf, not_lt]
  rw [heq]
  exact (isClosed_le continuous_const
    (continuous_dist_affine s t ((2 : ℝ) ^ i * minDist P * Real.sqrt (2 * samplingEps α)))).measurableSet

lemma measurableSet_targetBadSet {d : ℕ} (α : ℝ) (P : Finset (Pt d)) (s t : Pt d)
    (K L : ℕ) (i : Fin L) :
    MeasurableSet (targetBadSet α P s t K L i) := by
  unfold targetBadSet
  refine MeasurableSet.univ_pi fun ij => ?_
  by_cases h : ij.1 = i
  · rw [if_pos h]
    exact measurableSet_singleFailSet α P s t (i : ℕ)
  · rw [if_neg h]
    exact MeasurableSet.univ

lemma targetBadSet_measure_le {d : ℕ} [IsProbabilityMeasure (uniformSphere d)]
    {c₀ : ℝ} (hc₀_pos : 0 < c₀) (hc₀_lt1 : c₀ < 1)
    (h41 : ∀ (s t : Pt d) (r₀ : ℝ), s ≠ t → 0 < r₀ → r₀ ≤ dist s t → dist s t ≤ 2 * r₀ →
      ENNReal.ofReal c₀ ≤ uniformSphere d {u : Pt d |
        Covers (1 + 1 / (d : ℝ)) s
          (s + (r₀ * Real.sqrt (2 * samplingEps (1 + 1 / (d : ℝ)))) • u) t})
    (P : Finset (Pt d)) (hσ_pos : 0 < minDist P)
    (s t : Pt d) (hst : s ≠ t) (K L : ℕ) (i : Fin L)
    (hlo : (2 : ℝ) ^ (i : ℕ) * minDist P ≤ dist s t)
    (hhi : dist s t ≤ (2 : ℝ) ^ ((i : ℕ) + 1) * minDist P) :
    Measure.pi (fun _ : Fin L × Fin K => uniformSphere d)
      (targetBadSet (1 + 1 / (d : ℝ)) P s t K L i) ≤ ENNReal.ofReal ((1 - c₀) ^ K) := by
  let α : ℝ := 1 + 1 / (d : ℝ)
  let r₀ : ℝ := (2 : ℝ) ^ (i : ℕ) * minDist P
  have hr₀_pos : 0 < r₀ := by positivity
  have hhi' : dist s t ≤ 2 * r₀ := by
    have hp : (2 : ℝ) ^ ((i : ℕ) + 1) * minDist P = 2 * r₀ := by
      dsimp [r₀]
      ring
    linarith
  have hG_eq : (singleFailSet α P s t (i : ℕ))ᶜ =
      {w : Pt d | Covers α s (s + (r₀ * Real.sqrt (2 * samplingEps α)) • w) t} := by
    ext w
    simp [singleFailSet, scalePt, r₀, α]
  have hG_prob : ENNReal.ofReal c₀ ≤ uniformSphere d ((singleFailSet α P s t (i : ℕ))ᶜ) := by
    rw [hG_eq]
    exact h41 s t r₀ hst hr₀_pos hlo hhi'
  have hF_meas := measurableSet_singleFailSet α P s t (i : ℕ)
  have hF_prob : uniformSphere d (singleFailSet α P s t (i : ℕ)) ≤ ENNReal.ofReal (1 - c₀) := by
    have hsum1 : uniformSphere d (singleFailSet α P s t (i : ℕ)) +
        uniformSphere d ((singleFailSet α P s t (i : ℕ))ᶜ) = 1 := by
      rw [measure_add_measure_compl hF_meas, measure_univ]
    have hcompl : uniformSphere d (singleFailSet α P s t (i : ℕ)) =
        1 - uniformSphere d ((singleFailSet α P s t (i : ℕ))ᶜ) := by
      calc uniformSphere d (singleFailSet α P s t (i : ℕ))
          = (uniformSphere d (singleFailSet α P s t (i : ℕ)) +
              uniformSphere d ((singleFailSet α P s t (i : ℕ))ᶜ)) -
              uniformSphere d ((singleFailSet α P s t (i : ℕ))ᶜ) :=
            (ENNReal.add_sub_cancel_right (measure_ne_top _ _)).symm
        _ = 1 - uniformSphere d ((singleFailSet α P s t (i : ℕ))ᶜ) := by rw [hsum1]
    rw [hcompl]
    calc 1 - uniformSphere d ((singleFailSet α P s t (i : ℕ))ᶜ)
        ≤ 1 - ENNReal.ofReal c₀ := tsub_le_tsub_left hG_prob 1
      _ = ENNReal.ofReal 1 - ENNReal.ofReal c₀ := by rw [ENNReal.ofReal_one]
      _ = ENNReal.ofReal (1 - c₀) := (ENNReal.ofReal_sub 1 (le_of_lt hc₀_pos)).symm
  have hpi : Measure.pi (fun _ : Fin L × Fin K => uniformSphere d)
      (targetBadSet α P s t K L i) = (uniformSphere d (singleFailSet α P s t (i : ℕ))) ^ K := by
    unfold targetBadSet
    rw [Measure.pi_pi, Fintype.prod_prod_type, Fintype.prod_eq_single i]
    · simp
    · intro i' hi'
      simp [hi']
  rw [hpi, ENNReal.ofReal_pow (by linarith : 0 ≤ 1 - c₀) K]
  exact pow_le_pow_left' hF_prob K

end AuxCor42

open scoped Classical in
theorem solution : ∀ c : ℝ, 0 < c → ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧
    ∀ (d : ℕ), 1 ≤ d → ∀ P : Finset (Pt d), 2 ≤ P.card → ∀ s ∈ P,
      let α : ℝ := 1 + 1 / (d : ℝ)
      let n : ℝ := (P.card : ℝ)
      let K : ℕ := ⌈C * Real.log n⌉₊
      let L : ℕ := annulusCount P
      ((K : ℝ) * (L : ℝ) ≤ C' * ((L : ℝ) * Real.log n)) ∧
      (∀ u : Fin L × Fin K → Pt d, (annularCandidates α P s K L u).card ≤ K * L) ∧
      ENNReal.ofReal (1 - n ^ (-c)) ≤
        Measure.pi (fun _ : Fin L × Fin K => uniformSphere d)
          {u | CoversSet α s (annularCandidates α P s K L u) P} := by
  intro c hc
  obtain ⟨c₀_raw, hc₀_raw, h41_raw⟩ := SteinerNav.lemma_4_1
  set c₀ : ℝ := min c₀_raw (1 / 2)
  have hc₀_pos : 0 < c₀ := lt_min hc₀_raw (by norm_num)
  have hc₀_lt1 : c₀ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hc₀_le_raw : c₀ ≤ c₀_raw := min_le_left _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C : ℝ := (c + 1) / c₀
  set C' : ℝ := C + 1 / Real.log 2
  have hC : 0 < C := by positivity
  have hC' : 0 < C' := by positivity
  refine ⟨C, C', hC, hC', ?_⟩
  intro d hd P hn s hs
  dsimp only
  set α : ℝ := 1 + 1 / (d : ℝ)
  set K : ℕ := ⌈C * Real.log (P.card : ℝ)⌉₊
  set L : ℕ := annulusCount P
  have hn_ge2 : (2 : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hn
  have hn_pos : 0 < (P.card : ℝ) := by linarith
  have hlogn_ge : Real.log 2 ≤ Real.log (P.card : ℝ) := Real.log_le_log (by norm_num) hn_ge2
  have hlogn_pos : 0 < Real.log (P.card : ℝ) := lt_of_lt_of_le hlog2 hlogn_ge
  have hK_pos : 1 ≤ K := Nat.ceil_pos.mpr (by positivity)
  have hpart1 : (K : ℝ) * (L : ℝ) ≤ C' * ((L : ℝ) * Real.log (P.card : ℝ)) := by
    have hK_le : (K : ℝ) ≤ C * Real.log (P.card : ℝ) + 1 :=
      le_of_lt (Nat.ceil_lt_add_one (by positivity))
    have h1_le : 1 ≤ (1 / Real.log 2) * Real.log (P.card : ℝ) := by
      rw [one_div_mul_eq_div]
      exact (one_le_div hlog2).mpr hlogn_ge
    have hK_C' : (K : ℝ) ≤ C' * Real.log (P.card : ℝ) := by
      have hC'_def : C' = C + 1 / Real.log 2 := rfl
      rw [hC'_def]
      linarith
    calc (K : ℝ) * (L : ℝ) ≤ (C' * Real.log (P.card : ℝ)) * (L : ℝ) :=
          mul_le_mul_of_nonneg_right hK_C' (Nat.cast_nonneg L)
      _ = C' * ((L : ℝ) * Real.log (P.card : ℝ)) := by ring
  have hpart2 : ∀ u : Fin L × Fin K → Pt d, (annularCandidates α P s K L u).card ≤ K * L := by
    intro u
    unfold annularCandidates
    calc ((Finset.univ.filter fun ij : Fin L × Fin K => AnnulusNonempty P s (ij.1 : ℕ)).image _).card
        ≤ (Finset.univ.filter fun ij : Fin L × Fin K => AnnulusNonempty P s (ij.1 : ℕ)).card :=
          Finset.card_image_le
      _ ≤ (Finset.univ : Finset (Fin L × Fin K)).card := Finset.card_filter_le _ _
      _ = L * K := by simp
      _ = K * L := Nat.mul_comm L K
  refine ⟨hpart1, hpart2, ?_⟩
  have hprob_inst : IsProbabilityMeasure (uniformSphere d) := AuxCor42.isProb_uniformSphere hd hn
  have hσ_pos : 0 < minDist P := AuxCor42.minDist_pos_of_card P hn
  have h41_c₀ : ∀ (s' t' : Pt d) (r₀ : ℝ), s' ≠ t' → 0 < r₀ → r₀ ≤ dist s' t' →
      dist s' t' ≤ 2 * r₀ →
      ENNReal.ofReal c₀ ≤ uniformSphere d {u : Pt d |
        Covers α s' (s' + (r₀ * Real.sqrt (2 * samplingEps α)) • u) t'} := by
    intro s' t' r₀ hst' hr₀ hlo hhi
    exact le_trans (ENNReal.ofReal_le_ofReal hc₀_le_raw) (h41_raw d hd s' t' r₀ hst' hr₀ hlo hhi)
  have hex_idx : ∀ t : {x // x ∈ P.erase s}, ∃ i : Fin L,
      (2 : ℝ) ^ (i : ℕ) * minDist P ≤ dist s t.1 ∧
      dist s t.1 ≤ (2 : ℝ) ^ ((i : ℕ) + 1) * minDist P := by
    intro t
    obtain ⟨hts, htP⟩ := Finset.mem_erase.mp t.2
    obtain ⟨i, hiL, hlo, hhi⟩ := SteinerNav.annuli_cover_targets hd P hn s t.1 hs htP hts
    exact ⟨⟨i, hiL⟩, hlo, hhi⟩
  let idx : {x // x ∈ P.erase s} → Fin L := fun t => Classical.choose (hex_idx t)
  have hidx_spec : ∀ t : {x // x ∈ P.erase s},
      (2 : ℝ) ^ (idx t : ℕ) * minDist P ≤ dist s t.1 ∧
      dist s t.1 ≤ (2 : ℝ) ^ ((idx t : ℕ) + 1) * minDist P :=
    fun t => Classical.choose_spec (hex_idx t)
  let Bad : Set (Fin L × Fin K → Pt d) :=
    ⋃ t : {x // x ∈ P.erase s}, AuxCor42.targetBadSet α P s t.1 K L (idx t)
  have hBad_meas : MeasurableSet Bad :=
    MeasurableSet.iUnion fun t => AuxCor42.measurableSet_targetBadSet α P s t.1 K L (idx t)
  have hcompl_sub : Badᶜ ⊆ {u | CoversSet α s (annularCandidates α P s K L u) P} := by
    intro u hu t htP hts
    let tx : {x // x ∈ P.erase s} := ⟨t, Finset.mem_erase.mpr ⟨hts, htP⟩⟩
    have hunot : u ∉ AuxCor42.targetBadSet α P s tx.1 K L (idx tx) :=
      fun hm => hu (Set.mem_iUnion.mpr ⟨tx, hm⟩)
    by_contra hnocov
    apply hunot
    intro ij _
    dsimp only
    by_cases hij : ij.1 = idx tx
    · rw [if_pos hij]
      intro hcov_ij
      apply hnocov
      refine ⟨AuxCor42.scalePt α P s (ij.1 : ℕ) (u ij), ?_, ?_⟩
      · unfold annularCandidates AuxCor42.scalePt
        refine Finset.mem_image.mpr ⟨ij, Finset.mem_filter.mpr ⟨Finset.mem_univ ij, ?_⟩, rfl⟩
        obtain ⟨hlo, hhi⟩ := hidx_spec tx
        rw [hij]
        exact ⟨t, htP, hts, hlo, hhi⟩
      · rwa [hij]
    · rw [if_neg hij]
      trivial
  have hBad_union : Measure.pi (fun _ : Fin L × Fin K => uniformSphere d) Bad ≤
      ENNReal.ofReal ((P.card : ℝ) ^ (-c)) := by
    have hsum := measure_iUnion_fintype_le
      (Measure.pi fun _ : Fin L × Fin K => uniformSphere d)
      (fun t : {x // x ∈ P.erase s} => AuxCor42.targetBadSet α P s t.1 K L (idx t))
    have hsum_le : (∑ t : {x // x ∈ P.erase s},
        Measure.pi (fun _ : Fin L × Fin K => uniformSphere d)
          (AuxCor42.targetBadSet α P s t.1 K L (idx t))) ≤
        ∑ _t : {x // x ∈ P.erase s}, ENNReal.ofReal ((1 - c₀) ^ K) := by
      refine Finset.sum_le_sum fun t _ => ?_
      obtain ⟨hts, _⟩ := Finset.mem_erase.mp t.2
      obtain ⟨hlo, hhi⟩ := hidx_spec t
      exact AuxCor42.targetBadSet_measure_le hc₀_pos hc₀_lt1 h41_c₀ P hσ_pos s t.1
        hts.symm K L (idx t) hlo hhi
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe] at hsum_le
    have hTcard : ((P.erase s).card : ℝ) ≤ (P.card : ℝ) := by
      exact_mod_cast (Finset.card_erase_le : (P.erase s).card ≤ P.card)
    have hnsmul : (P.erase s).card • ENNReal.ofReal ((1 - c₀) ^ K) ≤
        ENNReal.ofReal ((P.card : ℝ) * (1 - c₀) ^ K) := by
      rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hTcard (pow_nonneg (by linarith) K))
    have hexp_bound : (P.card : ℝ) * (1 - c₀) ^ K ≤ (P.card : ℝ) ^ (-c) := by
      have h1mc : 1 - c₀ ≤ Real.exp (-c₀) := by linarith [Real.add_one_le_exp (-c₀)]
      have hpow_exp : (1 - c₀) ^ K ≤ Real.exp (-c₀ * (K : ℝ)) := by
        calc (1 - c₀) ^ K ≤ (Real.exp (-c₀)) ^ K :=
              pow_le_pow_left₀ (by linarith) h1mc K
          _ = Real.exp ((K : ℝ) * (-c₀)) := (Real.exp_nat_mul (-c₀) K).symm
          _ = Real.exp (-c₀ * (K : ℝ)) := by ring_nf
      have hK_ge : C * Real.log (P.card : ℝ) ≤ (K : ℝ) := Nat.le_ceil _
      have hcK : (c + 1) * Real.log (P.card : ℝ) ≤ c₀ * (K : ℝ) := by
        have h1 : c₀ * (C * Real.log (P.card : ℝ)) = (c + 1) * Real.log (P.card : ℝ) := by
          have hC_def : C = (c + 1) / c₀ := rfl
          rw [hC_def]
          field_simp
        nlinarith
      have hexp_le_rpow : Real.exp (-c₀ * (K : ℝ)) ≤ (P.card : ℝ) ^ (-(c + 1)) := by
        rw [Real.rpow_def_of_pos hn_pos]
        exact Real.exp_le_exp.mpr (by linarith)
      calc (P.card : ℝ) * (1 - c₀) ^ K
          ≤ (P.card : ℝ) * Real.exp (-c₀ * (K : ℝ)) :=
            mul_le_mul_of_nonneg_left hpow_exp (le_of_lt hn_pos)
        _ ≤ (P.card : ℝ) * (P.card : ℝ) ^ (-(c + 1)) :=
            mul_le_mul_of_nonneg_left hexp_le_rpow (le_of_lt hn_pos)
        _ = (P.card : ℝ) ^ (1 : ℝ) * (P.card : ℝ) ^ (-(c + 1)) := by rw [Real.rpow_one]
        _ = (P.card : ℝ) ^ ((1 : ℝ) + -(c + 1)) := (Real.rpow_add hn_pos _ _).symm
        _ = (P.card : ℝ) ^ (-c) := by ring_nf
    exact le_trans hsum (le_trans hsum_le (le_trans hnsmul (ENNReal.ofReal_le_ofReal hexp_bound)))
  have hBadc_eq : Measure.pi (fun _ : Fin L × Fin K => uniformSphere d) (Badᶜ) =
      1 - Measure.pi (fun _ : Fin L × Fin K => uniformSphere d) Bad :=
    prob_compl_eq_one_sub hBad_meas
  calc ENNReal.ofReal (1 - (P.card : ℝ) ^ (-c))
      = ENNReal.ofReal 1 - ENNReal.ofReal ((P.card : ℝ) ^ (-c)) :=
        ENNReal.ofReal_sub 1 (by positivity)
    _ = 1 - ENNReal.ofReal ((P.card : ℝ) ^ (-c)) := by rw [ENNReal.ofReal_one]
    _ ≤ 1 - Measure.pi (fun _ : Fin L × Fin K => uniformSphere d) Bad :=
        tsub_le_tsub_left hBad_union 1
    _ = Measure.pi (fun _ : Fin L × Fin K => uniformSphere d) (Badᶜ) := hBadc_eq.symm
    _ ≤ Measure.pi (fun _ : Fin L × Fin K => uniformSphere d)
          {u | CoversSet α s (annularCandidates α P s K L u) P} := measure_mono hcompl_sub
