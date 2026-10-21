-- Prove2me | solution 1 for PoWMining.CapacityStatics.aggregate_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:41:04.619893+00:00
-- url     : https://prove2.me/submissions/3b8e5b23-2860-4cde-8c6b-ba86cb1cd2b9

import Mathlib
import Definitions.Def_PoWMining_CapacityStatics_ClosedForms

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

theorem solution {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : PoWMining.CapacityStatics.Standing c γ R) :
    let C := PoWMining.CostStatics.cumCost c
    let g := PoWMining.CostStatics.gH c γ R
    let S := Real.sqrt (C ^ 2 + 4 * ((n : ℝ) - 1) * R * γ)
    HasDerivAt (fun x => PoWMining.CostStatics.gH c x R)
        (-((C ^ 2 + 2 * ((n : ℝ) - 1) * R * γ - C * S) / (2 * γ ^ 2 * S))) γ ∧
      -((C ^ 2 + 2 * ((n : ℝ) - 1) * R * γ - C * S) / (2 * γ ^ 2 * S)) = -(g ^ 2 / (C + 2 * γ * g)) ∧
      -(g ^ 2 / (C + 2 * γ * g)) < 0 ∧
    HasDerivAt (fun x => PoWMining.CostStatics.gH c γ x) (((n : ℝ) - 1) / S) R ∧
      ((n : ℝ) - 1) / S = ((n : ℝ) - 1) / (C + 2 * γ * g) ∧
      0 < ((n : ℝ) - 1) / (C + 2 * γ * g) := by
  intro C g S
  have hn := hS.two_le
  have hR := hS.R_pos
  have hγ := hS.γ_pos
  have hc := hS.c_pos
  obtain ⟨hg, hgS, hq⟩ := gH_facts c hn hc γ R hγ hR
  have hCpos := C_pos c hn hc
  have hm := m_pos hn
  have hgS' : C + 2 * γ * g = S := hgS
  have hg' : 0 < g := hg
  have hCp : 0 < C := hCpos
  have hSpos : 0 < S := by
    have : 0 < 4 * ((n : ℝ) - 1) * R * γ := by positivity
    show 0 < Real.sqrt (C ^ 2 + 4 * ((n : ℝ) - 1) * R * γ)
    positivity
  have hS2 : S ^ 2 = C ^ 2 + 4 * ((n : ℝ) - 1) * R * γ := Real.sq_sqrt (by positivity)
  have hgeq : g = (S - C) / (2 * γ) := gH_eq c γ R hγ
  have E1 : -((C ^ 2 + 2 * ((n : ℝ) - 1) * R * γ - C * S) / (2 * γ ^ 2 * S)) = -(g ^ 2 / (C + 2 * γ * g)) := by
    rw [hgS']
    rw [alg_E1 C S ((n : ℝ) - 1) R γ hγ hSpos hS2, ← hgeq]
  refine ⟨(hasDerivAt_g_gamma c hn hc γ R hγ hR).congr_deriv E1.symm, E1, ?_, ?_, ?_, ?_⟩
  · exact neg_neg_of_pos (div_pos (pow_pos hg' 2) (by rw [hgS']; exact hSpos))
  · rw [← hgS']; exact hasDerivAt_g_R c hn hc γ R hγ hR
  · rw [hgS']
  · exact div_pos (by linarith) (by rw [hgS']; exact hSpos)
