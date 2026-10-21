-- Prove2me | solution 1 for PoWMining.CapacityStatics.proposition_4_8
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:52:50.892513+00:00
-- url     : https://prove2.me/submissions/baa80ee3-a7f8-48ef-9706-163d9c90dafd

import Mathlib
import Definitions.Def_PoWMining_CapacityStatics_ClosedForms
import Definitions.Def_PoWMining_CapacityStatics_Sensitivities

set_option autoImplicit false
open Filter Topology
open PoWMining.CostStatics (cumCost gH fH hstar share)

lemma C_pos {n : ℕ} (c : Fin n → ℝ) (hn : 2 ≤ n) (hc : ∀ k, 0 < c k) : 0 < cumCost c := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  exact Finset.sum_pos (fun k _ => hc k) Finset.univ_nonempty

lemma m_pos {n : ℕ} (hn : 2 ≤ n) : (1 : ℝ) ≤ (n : ℝ) - 1 := by
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

lemma gH_eq {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hγ : 0 < γ) :
    gH c γ R = (Real.sqrt (cumCost c ^ 2 + 4 * ((n : ℝ) - 1) * R * γ) - cumCost c) / (2 * γ) := by
  unfold gH; rw [if_pos hγ]

lemma g_alg (C S m R γ : ℝ) (hγ : 0 < γ) (hS2 : S ^ 2 = C ^ 2 + 4 * m * R * γ) (hSC : C < S) :
    0 < (S - C) / (2 * γ) ∧ C + 2 * γ * ((S - C) / (2 * γ)) = S ∧
    γ * ((S - C) / (2 * γ)) ^ 2 + C * ((S - C) / (2 * γ)) = m * R := by
  refine ⟨div_pos (by linarith) (by positivity), ?_, ?_⟩
  · field_simp; ring
  · field_simp
    nlinarith [hS2]

lemma gH_facts {n : ℕ} (c : Fin n → ℝ) (hn : 2 ≤ n) (hc : ∀ k, 0 < c k) (γ R : ℝ)
    (hγ : 0 < γ) (hR : 0 < R) :
    0 < gH c γ R ∧ cumCost c + 2 * γ * gH c γ R = Real.sqrt (cumCost c ^ 2 + 4 * ((n : ℝ) - 1) * R * γ) ∧
    γ * gH c γ R ^ 2 + cumCost c * gH c γ R = ((n : ℝ) - 1) * R := by
  have hC := C_pos c hn hc
  have hm := m_pos hn
  have hpos : 0 < 4 * ((n : ℝ) - 1) * R * γ := by positivity
  have hS2 : Real.sqrt (cumCost c ^ 2 + 4 * ((n : ℝ) - 1) * R * γ) ^ 2
      = cumCost c ^ 2 + 4 * ((n : ℝ) - 1) * R * γ := Real.sq_sqrt (by positivity)
  have hSC : cumCost c < Real.sqrt (cumCost c ^ 2 + 4 * ((n : ℝ) - 1) * R * γ) :=
    (Real.lt_sqrt hC.le).2 (by linarith)
  rw [gH_eq c γ R hγ]
  exact g_alg _ _ _ _ _ hγ hS2 hSC

lemma hasDerivAt_g_gamma {n : ℕ} (c : Fin n → ℝ) (hn : 2 ≤ n) (hc : ∀ k, 0 < c k) (γ R : ℝ)
    (hγ : 0 < γ) (hR : 0 < R) :
    HasDerivAt (fun x => gH c x R)
      (-(gH c γ R ^ 2 / (cumCost c + 2 * γ * gH c γ R))) γ := by
  obtain ⟨hg, hgS, hq⟩ := gH_facts c hn hc γ R hγ hR
  have hC := C_pos c hn hc
  have hm := m_pos hn
  have hev : (fun x => gH c x R) =ᶠ[𝓝 γ] fun x =>
      (Real.sqrt (cumCost c ^ 2 + 4 * ((n : ℝ) - 1) * R * x) - cumCost c) / (2 * x) := by
    filter_upwards [eventually_gt_nhds hγ] with x hx
    exact gH_eq c x R hx
  have h1 : HasDerivAt (fun x : ℝ => cumCost c ^ 2 + 4 * ((n : ℝ) - 1) * R * x)
      (4 * ((n : ℝ) - 1) * R) γ := by
    simpa using ((hasDerivAt_id γ).const_mul (4 * ((n : ℝ) - 1) * R)).const_add (cumCost c ^ 2)
  have hne : cumCost c ^ 2 + 4 * ((n : ℝ) - 1) * R * γ ≠ 0 := by positivity
  have h2 := h1.sqrt hne
  have h3 := (h2.sub_const (cumCost c)).div ((hasDerivAt_id γ).const_mul 2) (by simp; positivity)
  refine (h3.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [hgS, gH_eq c γ R hγ]
  have hS2 : Real.sqrt (cumCost c ^ 2 + 4 * ((n : ℝ) - 1) * R * γ) ^ 2
      = cumCost c ^ 2 + 4 * ((n : ℝ) - 1) * R * γ := Real.sq_sqrt (by positivity)
  have hSpos : 0 < Real.sqrt (cumCost c ^ 2 + 4 * ((n : ℝ) - 1) * R * γ) := by positivity
  set C := cumCost c
  set S := Real.sqrt (C ^ 2 + 4 * ((n : ℝ) - 1) * R * γ)
  have key : 4 * ((n : ℝ) - 1) * R = (S ^ 2 - C ^ 2) / γ := by
    rw [eq_div_iff hγ.ne']; linarith
  simp only [id]
  rw [key]
  field_simp
  ring

lemma hasDerivAt_g_R {n : ℕ} (c : Fin n → ℝ) (hn : 2 ≤ n) (hc : ∀ k, 0 < c k) (γ R : ℝ)
    (hγ : 0 < γ) (hR : 0 < R) :
    HasDerivAt (fun x => gH c γ x)
      (((n : ℝ) - 1) / (cumCost c + 2 * γ * gH c γ R)) R := by
  obtain ⟨hg, hgS, hq⟩ := gH_facts c hn hc γ R hγ hR
  have hC := C_pos c hn hc
  have hm := m_pos hn
  have hfun : (fun x => gH c γ x) = fun x =>
      (Real.sqrt (cumCost c ^ 2 + 4 * ((n : ℝ) - 1) * x * γ) - cumCost c) / (2 * γ) := by
    funext x; exact gH_eq c γ x hγ
  rw [hfun]
  have h1 : HasDerivAt (fun x : ℝ => cumCost c ^ 2 + 4 * ((n : ℝ) - 1) * x * γ)
      (4 * ((n : ℝ) - 1) * γ) R := by
    simpa using (((hasDerivAt_id R).const_mul (4 * ((n : ℝ) - 1))).mul_const γ).const_add (cumCost c ^ 2)
  have hne : cumCost c ^ 2 + 4 * ((n : ℝ) - 1) * R * γ ≠ 0 := by positivity
  have h2 := h1.sqrt hne
  have h3 := (h2.sub_const (cumCost c)).div_const (2 * γ)
  refine h3.congr_deriv ?_
  rw [hgS]
  have hSpos : 0 < Real.sqrt (cumCost c ^ 2 + 4 * ((n : ℝ) - 1) * R * γ) := by positivity
  field_simp
  ring

lemma alg_E1 (C S m R γ : ℝ) (hγ : 0 < γ) (hS0 : 0 < S) (hS2 : S ^ 2 = C ^ 2 + 4 * m * R * γ) :
    -((C ^ 2 + 2 * m * R * γ - C * S) / (2 * γ ^ 2 * S)) = -(((S - C) / (2 * γ)) ^ 2 / S) := by
  have key3 : 2 * m * R * γ = (S ^ 2 - C ^ 2) / 2 := by linarith
  rw [key3]
  field_simp
  ring

lemma hasDerivAt_fG {n : ℕ} (c : Fin n → ℝ) (γ R G : ℝ) (i : Fin n) (hD : R + γ * G ^ 2 ≠ 0) :
    HasDerivAt (fun G => fH c γ R G i) (R * (R - γ * G ^ 2 - 2 * c i * G) / (R + γ * G ^ 2) ^ 2) G := by
  have hnum : HasDerivAt (fun G : ℝ => G * (R - c i * G)) (R - 2 * c i * G) G := by
    have := (hasDerivAt_id G).mul (((hasDerivAt_id G).const_mul (c i)).const_sub R)
    exact this.congr_deriv (by simp only [id]; ring)
  have hden : HasDerivAt (fun G : ℝ => R + γ * G ^ 2) (2 * γ * G) G := by
    have := ((hasDerivAt_pow 2 G).const_mul γ).const_add R
    exact this.congr_deriv (by norm_num <;> ring)
  have := hnum.div hden hD
  refine this.congr_deriv ?_
  field_simp
  ring

lemma hasDerivAt_f_gamma {n : ℕ} (c : Fin n → ℝ) (γ R G : ℝ) (i : Fin n) (hD : R + γ * G ^ 2 ≠ 0) :
    HasDerivAt (fun x => fH c x R G i) (-(G ^ 3 * ((R - c i * G) / (R + γ * G ^ 2) ^ 2))) γ := by
  have h1 : HasDerivAt (fun x : ℝ => R + x * G ^ 2) (G ^ 2) γ := by
    simpa using ((hasDerivAt_id γ).mul_const (G ^ 2)).const_add R
  have h2 := (hasDerivAt_const γ (G * (R - c i * G))).div h1 hD
  refine h2.congr_deriv ?_
  field_simp
  ring

lemma hasDerivAt_f_R {n : ℕ} (c : Fin n → ℝ) (γ R G : ℝ) (i : Fin n) (hD : R + γ * G ^ 2 ≠ 0) :
    HasDerivAt (fun x => fH c γ x G i) (G ^ 2 * ((c i + γ * G) / (R + γ * G ^ 2) ^ 2)) R := by
  have h1 : HasDerivAt (fun x : ℝ => G * (x - c i * G)) G R := by
    simpa using ((hasDerivAt_id R).sub_const (c i * G)).const_mul G
  have h2 : HasDerivAt (fun x : ℝ => x + γ * G ^ 2) 1 R := by
    simpa using (hasDerivAt_id R).add_const (γ * G ^ 2)
  have h3 := h1.div h2 hD
  refine h3.congr_deriv ?_
  field_simp
  ring

lemma hstar_deriv_gamma {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (i : Fin n) (gg : ℝ)
    (hg : HasDerivAt (fun x => gH c x R) gg γ) (hD : R + γ * gH c γ R ^ 2 ≠ 0) :
    HasDerivAt (fun x => hstar c x R i)
      (-(gH c γ R ^ 3 * ((R - c i * gH c γ R) / (R + γ * gH c γ R ^ 2) ^ 2))
        + (R * (R - γ * gH c γ R ^ 2 - 2 * c i * gH c γ R) / (R + γ * gH c γ R ^ 2) ^ 2) * gg) γ := by
  have hnum := hg.mul ((hg.const_mul (c i)).const_sub R)
  have hden := ((hasDerivAt_id γ).mul (hg.pow 2)).const_add R
  have h := hnum.div hden hD
  refine h.congr_deriv ?_
  try simp only [id]
  try norm_num
  field_simp
  ring

lemma hstar_deriv_R {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (i : Fin n) (gr : ℝ)
    (hg : HasDerivAt (fun x => gH c γ x) gr R) (hD : R + γ * gH c γ R ^ 2 ≠ 0) :
    HasDerivAt (fun x => hstar c γ x i)
      (gH c γ R ^ 2 * ((c i + γ * gH c γ R) / (R + γ * gH c γ R ^ 2) ^ 2)
        + (R * (R - γ * gH c γ R ^ 2 - 2 * c i * gH c γ R) / (R + γ * gH c γ R ^ 2) ^ 2) * gr) R := by
  have hnum := hg.mul (((hasDerivAt_id R).sub (hg.const_mul (c i))))
  have hden := (hasDerivAt_id R).add ((hg.pow 2).const_mul γ)
  have h := hnum.div hden hD
  refine h.congr_deriv ?_
  try simp only [id]
  try norm_num
  field_simp
  ring

open PoWMining.CapacityStatics (DeltaG1 DeltaG2 DeltaR1 DeltaR2)

theorem solution {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : PoWMining.CapacityStatics.Standing c γ R) :
    (∀ i, HasDerivAt (fun x => PoWMining.CostStatics.hstar c x R i) (DeltaG1 c γ R i + DeltaG2 c γ R i) γ ∧
        DeltaG1 c γ R i < 0 ∧ (0 < DeltaG2 c γ R i ↔ PoWMining.CostStatics.share c γ R i < 1 / 2)) ∧
    (∀ i, HasDerivAt (fun x => PoWMining.CostStatics.hstar c γ x i) (DeltaR1 c γ R i + DeltaR2 c γ R i) R ∧
        0 < DeltaR1 c γ R i + DeltaR2 c γ R i ∧ 0 < DeltaR1 c γ R i ∧
        (DeltaR2 c γ R i < 0 ↔ PoWMining.CostStatics.share c γ R i < 1 / 2)) ∧
    ∃ dγ dR : Fin n → ℝ,
      (∀ i, HasDerivAt (fun x => PoWMining.CostStatics.share c x R i) (dγ i) γ) ∧
      (∀ i, HasDerivAt (fun x => PoWMining.CostStatics.share c γ x i) (dR i) R) ∧
      Monotone dγ ∧ Monotone dR := by
  have hn := hS.two_le
  have hR := hS.R_pos
  have hγ := hS.γ_pos
  have hc := hS.c_pos
  have hCpos := C_pos c hn hc
  have hm := m_pos hn
  obtain ⟨hg, hgS, hq⟩ := gH_facts c hn hc γ R hγ hR
  have hgG0 := hasDerivAt_g_gamma c hn hc γ R hγ hR
  have hgR0 := hasDerivAt_g_R c hn hc γ R hγ hR
  have hact0 := hS.active
  obtain ⟨g, hgdef⟩ : ∃ g, gH c γ R = g := ⟨_, rfl⟩
  rw [hgdef] at hg hgS hq hgG0 hgR0
  have hact : ∀ i, 0 < R - c i * g := fun i => by have := hact0 i; rwa [hgdef] at this
  obtain ⟨gg, hggdef⟩ : ∃ gg, gg = -(g ^ 2 / (cumCost c + 2 * γ * g)) := ⟨_, rfl⟩
  obtain ⟨gr, hgrdef⟩ : ∃ gr, gr = ((n : ℝ) - 1) / (cumCost c + 2 * γ * g) := ⟨_, rfl⟩
  rw [← hggdef] at hgG0
  rw [← hgrdef] at hgR0
  have hSpos : 0 < cumCost c + 2 * γ * g := by positivity
  have hD : 0 < R + γ * g ^ 2 := by positivity
  have hDne : R + γ * gH c γ R ^ 2 ≠ 0 := by rw [hgdef]; exact hD.ne'
  have hggS : gg * (cumCost c + 2 * γ * g) = -g ^ 2 := by
    rw [hggdef]; field_simp
  have hgrS : gr * (cumCost c + 2 * γ * g) = (n : ℝ) - 1 := by
    rw [hgrdef]; field_simp
  have hgr_pos : 0 < gr := by rw [hgrdef]; exact div_pos (by linarith) hSpos
  have hgg_neg : gg < 0 := by rw [hggdef]; exact neg_neg_of_pos (div_pos (pow_pos hg 2) hSpos)
  -- closed forms of the Delta quantities
  have hDG1 : ∀ i, DeltaG1 c γ R i = -(g ^ 3 * ((R - c i * g) / (R + γ * g ^ 2) ^ 2)) := fun i => by
    unfold PoWMining.CapacityStatics.DeltaG1
    rw [(hasDerivAt_f_gamma c γ R (gH c γ R) i hDne).deriv, hgdef]
  have hDG2 : ∀ i, DeltaG2 c γ R i
      = (R * (R - γ * g ^ 2 - 2 * c i * g) / (R + γ * g ^ 2) ^ 2) * gg := fun i => by
    unfold PoWMining.CapacityStatics.DeltaG2
    rw [(hasDerivAt_fG c γ R (gH c γ R) i hDne).deriv, hgG0.deriv, hgdef]
  have hDR1 : ∀ i, DeltaR1 c γ R i = g ^ 2 * ((c i + γ * g) / (R + γ * g ^ 2) ^ 2) := fun i => by
    unfold PoWMining.CapacityStatics.DeltaR1
    rw [(hasDerivAt_f_R c γ R (gH c γ R) i hDne).deriv, hgdef]
  have hDR2 : ∀ i, DeltaR2 c γ R i
      = (R * (R - γ * g ^ 2 - 2 * c i * g) / (R + γ * g ^ 2) ^ 2) * gr := fun i => by
    unfold PoWMining.CapacityStatics.DeltaR2
    rw [(hasDerivAt_fG c γ R (gH c γ R) i hDne).deriv, hgR0.deriv, hgdef]
  have hstar_i : ∀ i, hstar c γ R i = g * (R - c i * g) / (R + γ * g ^ 2) := fun i => by
    unfold PoWMining.CostStatics.hstar PoWMining.CostStatics.fH
    rw [hgdef]
  have share_i : ∀ i, share c γ R i = (R - c i * g) / (R + γ * g ^ 2) := fun i => by
    unfold PoWMining.CostStatics.share
    rw [hstar_i, hgdef]; field_simp
  have share_iff : ∀ i, share c γ R i < 1 / 2 ↔ R - γ * g ^ 2 - 2 * c i * g < 0 := fun i => by
    rw [share_i, div_lt_iff₀ hD]
    constructor <;> intro h <;> linarith
  -- the derivatives of hstar
  have hHγ : ∀ i, HasDerivAt (fun x => hstar c x R i) (DeltaG1 c γ R i + DeltaG2 c γ R i) γ := fun i => by
    have := hstar_deriv_gamma c γ R i gg hgG0 hDne
    rw [hgdef] at this
    rw [hDG1, hDG2]
    exact this
  have hHR : ∀ i, HasDerivAt (fun x => hstar c γ x i) (DeltaR1 c γ R i + DeltaR2 c γ R i) R := fun i => by
    have := hstar_deriv_R c γ R i gr hgR0 hDne
    rw [hgdef] at this
    rw [hDR1, hDR2]
    exact this
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine ⟨hHγ i, ?_, ?_⟩
    · rw [hDG1]
      exact neg_neg_of_pos (mul_pos (pow_pos hg 3) (div_pos (hact i) (pow_pos hD 2)))
    · rw [share_iff, hDG2]
      have hκ : 0 < R * g ^ 2 / ((R + γ * g ^ 2) ^ 2 * (cumCost c + 2 * γ * g)) := by positivity
      have hid : (R * (R - γ * g ^ 2 - 2 * c i * g) / (R + γ * g ^ 2) ^ 2) * gg
          = -((R * g ^ 2 / ((R + γ * g ^ 2) ^ 2 * (cumCost c + 2 * γ * g)))
              * (R - γ * g ^ 2 - 2 * c i * g)) := by
        rw [hggdef]; field_simp
      rw [hid]
      constructor
      · intro h
        by_contra hcon
        push Not at hcon
        have := mul_nonneg hκ.le hcon
        linarith
      · intro h
        have := mul_neg_of_pos_of_neg hκ h
        linarith
  · intro i
    have hpos1 : 0 < DeltaR1 c γ R i := by
      rw [hDR1]; exact mul_pos (pow_pos hg 2) (div_pos (by have := hc i; positivity) (pow_pos hD 2))
    refine ⟨hHR i, ?_, hpos1, ?_⟩
    · rw [hDR1, hDR2]
      have hnum : (g ^ 2 * ((c i + γ * g) / (R + γ * g ^ 2) ^ 2)
          + (R * (R - γ * g ^ 2 - 2 * c i * g) / (R + γ * g ^ 2) ^ 2) * gr)
            * ((R + γ * g ^ 2) ^ 2 * (cumCost c + 2 * γ * g))
          = g ^ 2 * (c i + γ * g) * (cumCost c + 2 * γ * g)
            + R * (R - γ * g ^ 2 - 2 * c i * g) * (gr * (cumCost c + 2 * γ * g)) := by
        field_simp
      rw [hgrS] at hnum
      have hkey : g ^ 2 * (c i + γ * g) * (cumCost c + 2 * γ * g)
            + R * (R - γ * g ^ 2 - 2 * c i * g) * ((n : ℝ) - 1)
          = γ ^ 2 * g ^ 4 + γ * R * g ^ 2 + cumCost c * g * (R - c i * g) := by
        linear_combination (-(R - γ * g ^ 2 - 2 * c i * g)) * hq
      have hpos : 0 < γ ^ 2 * g ^ 4 + γ * R * g ^ 2 + cumCost c * g * (R - c i * g) := by
        have := hact i
        positivity
      rw [hkey] at hnum
      have h2 : 0 < (R + γ * g ^ 2) ^ 2 * (cumCost c + 2 * γ * g) := by positivity
      by_contra hcon
      push Not at hcon
      have := mul_nonpos_of_nonpos_of_nonneg hcon h2.le
      linarith
    · rw [share_iff, hDR2]
      have hκ : 0 < R * gr / (R + γ * g ^ 2) ^ 2 := by positivity
      have hid : (R * (R - γ * g ^ 2 - 2 * c i * g) / (R + γ * g ^ 2) ^ 2) * gr
          = (R * gr / (R + γ * g ^ 2) ^ 2) * (R - γ * g ^ 2 - 2 * c i * g) := by
        field_simp
      rw [hid]
      constructor
      · intro h
        by_contra hcon
        push Not at hcon
        have := mul_nonneg hκ.le hcon
        linarith
      · intro h
        exact mul_neg_of_pos_of_neg hκ h
  · -- the shares
    set E : ℝ := g ^ 3 + gg * (γ * g ^ 2 - R) with hE_def
    set ER : ℝ := g + gr * (γ * g ^ 2 - R) with hER_def
    have hE : E * (cumCost c + 2 * γ * g) = g ^ 2 * (((n : ℝ) - 1 + 1) * R) := by
      have h1 : E * (cumCost c + 2 * γ * g)
          = g ^ 3 * (cumCost c + 2 * γ * g) + (gg * (cumCost c + 2 * γ * g)) * (γ * g ^ 2 - R) := by
        rw [hE_def]; ring
      rw [h1, hggS]
      linear_combination g ^ 2 * hq
    have hERS : ER * (cumCost c + 2 * γ * g) = ((n : ℝ) - 1 + 1) * γ * g ^ 2 := by
      have h1 : ER * (cumCost c + 2 * γ * g)
          = g * (cumCost c + 2 * γ * g) + (gr * (cumCost c + 2 * γ * g)) * (γ * g ^ 2 - R) := by
        rw [hER_def]; ring
      rw [h1, hgrS]
      linear_combination hq
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 + 1 := by linarith
    have hEpos : 0 < E := by
      have h1 : 0 < E * (cumCost c + 2 * γ * g) := by
        rw [hE]; positivity
      by_contra hcon
      push Not at hcon
      nlinarith
    have hERpos : 0 < ER := by
      have h1 : 0 < ER * (cumCost c + 2 * γ * g) := by
        rw [hERS]; positivity
      by_contra hcon
      push Not at hcon
      nlinarith
    refine ⟨fun i => (c i * E - R * g * (g + 2 * γ * gg)) / (R + γ * g ^ 2) ^ 2,
      fun i => (c i * ER + (γ * g ^ 2 - 2 * R * γ * g * gr)) / (R + γ * g ^ 2) ^ 2, ?_, ?_, ?_, ?_⟩
    · intro i
      have h1 := (hstar_deriv_gamma c γ R i gg hgG0 hDne).div hgG0 (by rw [hgdef]; exact hg.ne')
      rw [hgdef] at h1
      refine h1.congr_deriv ?_
      rw [hstar_i]
      rw [hE_def]
      field_simp
      ring
    · intro i
      have h1 := (hstar_deriv_R c γ R i gr hgR0 hDne).div hgR0 (by rw [hgdef]; exact hg.ne')
      rw [hgdef] at h1
      refine h1.congr_deriv ?_
      rw [hstar_i]
      rw [hER_def]
      field_simp
      ring
    · intro i j hij
      have hcij : c i ≤ c j := hS.c_mono hij
      have hD2 : 0 < (R + γ * g ^ 2) ^ 2 := by positivity
      apply div_le_div_of_nonneg_right _ hD2.le
      nlinarith [mul_le_mul_of_nonneg_right hcij hEpos.le]
    · intro i j hij
      have hcij : c i ≤ c j := hS.c_mono hij
      have hD2 : 0 < (R + γ * g ^ 2) ^ 2 := by positivity
      apply div_le_div_of_nonneg_right _ hD2.le
      nlinarith [mul_le_mul_of_nonneg_right hcij hERpos.le]
