-- Prove2me | solution 1 for OutlierAssort.ActiveElim.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T17:26:09.824145+00:00
-- url     : https://prove2.me/submissions/288390bb-6e65-4b1e-85e8-883dbf655f80

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_OutlierAssort_ActiveElim_Model
import Definitions.Def_OutlierAssort_ActiveElim_Algorithm
import Theorems.Thm_OutlierAssort_ActiveElim_lemma_2

open OutlierAssort.ActiveElim

namespace OACor

theorem estimate_mem (n n0 : ℕ) : estimate n n0 ∈ Set.Icc (0 : ℝ) 1 := by
  unfold estimate
  split_ifs
  · exact ⟨zero_le_one, le_rfl⟩
  · exact ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩

theorem vhat_mem {N : ℕ} (alg : Input N) {t : ℕ} (p : Fin t → Rec N) :
    ∀ τ i, (state alg p τ).vhat i ∈ Set.Icc (0 : ℝ) 1 := by
  intro τ
  induction τ with
  | zero => intro i; exact ⟨zero_le_one, le_rfl⟩
  | succ τ ih =>
    intro i
    simp only [state]
    split_ifs
    · exact estimate_mem _ _
    · exact ih i

theorem rev_mem {N : ℕ} (r w : Fin N → ℝ) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (hw : ∀ i, 0 ≤ w i) (S : Finset (Fin N)) : rev r w S ∈ Set.Icc (0 : ℝ) 1 := by
  unfold rev ChoiceCDLP.MNL.mnlObjective
  have h0 := Finset.sum_nonneg (fun j (_ : j ∈ S) => hw j)
  refine ⟨div_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hr i).1 (hw i))) (by linarith), ?_⟩
  rw [div_le_one (by linarith)]
  have : ∑ j ∈ S, r j * w j ≤ ∑ j ∈ S, w j := Finset.sum_le_sum (fun i _ => by
    have := (hr i).2; have := hw i; nlinarith)
  linarith

theorem abs_rev_sub_le_one {N : ℕ} (r w v : Fin N → ℝ) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i) (S : Finset (Fin N)) :
    |rev r w S - rev r v S| ≤ 1 := by
  have h1 := rev_mem r w hr hw S
  have h2 := rev_mem r v hr hv S
  rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- The deterministic core of Corollary 1. -/
theorem core_bound {N : ℕ} (K : ℕ) (r v vhat : Fin N → ℝ) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ i, v i ∈ Set.Icc (0 : ℝ) 1) (hvhat : ∀ i, 0 ≤ vhat i) (S : Finset (Fin N))
    (hSK : S.card ≤ K) (B c : ℝ) (hB : 0 ≤ B) (hc : 0 ≤ c) (V' : Fin N → ℝ)
    (hV' : ∀ i ∈ S, 0 ≤ V' i ∧ V' i ≤ K)
    (hest : ∀ i ∈ S, |vhat i - v i| ≤ 8 * ((K : ℝ) + 1) * B + 8 * Real.sqrt ((1 + V' i) * v i * c)) :
    |rev r vhat S - rev r v S| ≤
      16 * K * ((K : ℝ) + 1) * B + Real.sqrt ((K : ℝ) + 1) / 2 * (16 * Real.sqrt (K * c)) := by
  have hl2 := OutlierAssort.ActiveElim.lemma_2 r v vhat hr hv hvhat S
  set V := ∑ i ∈ S, v i with hVdef
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun i _ => (hv i).1)
  have hpos : 0 < 1 + V := by linarith
  have hKr : (0 : ℝ) ≤ K := by positivity
  have hScard : (S.card : ℝ) ≤ K := by exact_mod_cast hSK
  -- bound each estimation error
  have hsqrt_i : ∀ i ∈ S, Real.sqrt ((1 + V' i) * v i * c) ≤
      Real.sqrt ((K : ℝ) + 1) * Real.sqrt c * Real.sqrt (v i) := by
    intro i hi
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    have h1 : 1 + V' i ≤ (K : ℝ) + 1 := by linarith [(hV' i hi).2]
    have h2 : 0 ≤ v i * c := mul_nonneg (hv i).1 hc
    nlinarith
  have hsum : ∑ i ∈ S, |vhat i - v i| ≤
      S.card * (8 * ((K : ℝ) + 1) * B) +
        8 * (Real.sqrt ((K : ℝ) + 1) * Real.sqrt c) * ∑ i ∈ S, Real.sqrt (v i) := by
    calc ∑ i ∈ S, |vhat i - v i| ≤ ∑ i ∈ S, (8 * ((K : ℝ) + 1) * B +
          8 * (Real.sqrt ((K : ℝ) + 1) * Real.sqrt c * Real.sqrt (v i))) := by
          apply Finset.sum_le_sum
          intro i hi
          have := hsqrt_i i hi
          have := hest i hi
          linarith
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl (fun i _ => by ring)
  -- Cauchy–Schwarz
  have hcs : ∑ i ∈ S, Real.sqrt (v i) ≤ Real.sqrt K * Real.sqrt V := by
    rw [← Real.sqrt_mul hKr]
    apply Real.le_sqrt_of_sq_le
    have := sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => Real.sqrt (v i))
    have e : ∑ i ∈ S, Real.sqrt (v i) ^ 2 = V :=
      Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (hv i).1)
    rw [e] at this
    calc _ ≤ (S.card : ℝ) * V := this
      _ ≤ K * V := mul_le_mul_of_nonneg_right hScard hV0
  have hamgm : 2 * Real.sqrt V ≤ 1 + V := by
    have := Real.sq_sqrt hV0
    nlinarith [sq_nonneg (Real.sqrt V - 1)]
  -- assemble
  set s1 := Real.sqrt ((K : ℝ) + 1) with hs1
  set s2 := Real.sqrt c with hs2
  have hs10 : 0 ≤ s1 := Real.sqrt_nonneg _
  have hs20 : 0 ≤ s2 := Real.sqrt_nonneg _
  have hKc : Real.sqrt (K * c) = Real.sqrt K * s2 := Real.sqrt_mul hKr c
  have hsK := Real.sqrt_nonneg (K : ℝ)
  have hsV := Real.sqrt_nonneg V
  -- 2 * (first part) / (1+V) ≤ 16K(K+1)B
  have hA : 2 * ((S.card : ℝ) * (8 * ((K : ℝ) + 1) * B)) ≤
      (1 + V) * (16 * K * ((K : ℝ) + 1) * B) := by
    have h1 : 0 ≤ 16 * ((K : ℝ) + 1) * B := by positivity
    have h2 : (S.card : ℝ) * (16 * ((K : ℝ) + 1) * B) ≤ K * (16 * ((K : ℝ) + 1) * B) :=
      mul_le_mul_of_nonneg_right hScard h1
    have h3 : K * (16 * ((K : ℝ) + 1) * B) ≤ (1 + V) * (K * (16 * ((K : ℝ) + 1) * B)) := by
      have : 0 ≤ K * (16 * ((K : ℝ) + 1) * B) := by positivity
      nlinarith
    nlinarith
  have hBpart : 2 * (8 * (s1 * s2) * ∑ i ∈ S, Real.sqrt (v i)) ≤
      (1 + V) * (s1 / 2 * (16 * (Real.sqrt K * s2))) := by
    have h1 : 2 * (8 * (s1 * s2) * ∑ i ∈ S, Real.sqrt (v i)) ≤
        16 * (s1 * s2) * (Real.sqrt K * Real.sqrt V) := by
      have : 0 ≤ 16 * (s1 * s2) := by positivity
      nlinarith
    have h2 : 16 * (s1 * s2) * (Real.sqrt K * Real.sqrt V) =
        (8 * (s1 * s2 * Real.sqrt K)) * (2 * Real.sqrt V) := by ring
    have h3 : (8 * (s1 * s2 * Real.sqrt K)) * (2 * Real.sqrt V) ≤
        (8 * (s1 * s2 * Real.sqrt K)) * (1 + V) :=
      mul_le_mul_of_nonneg_left hamgm (by positivity)
    have h4 : (8 * (s1 * s2 * Real.sqrt K)) * (1 + V) = (1 + V) * (s1 / 2 * (16 * (Real.sqrt K * s2))) := by
      ring
    linarith
  calc |rev r vhat S - rev r v S| ≤ 2 * (∑ i ∈ S, |vhat i - v i|) / (1 + V) := hl2
    _ ≤ 2 * (S.card * (8 * ((K : ℝ) + 1) * B) +
        8 * (s1 * s2) * ∑ i ∈ S, Real.sqrt (v i)) / (1 + V) := by
        apply div_le_div_of_nonneg_right _ hpos.le
        linarith
    _ ≤ 16 * K * ((K : ℝ) + 1) * B + s1 / 2 * (16 * Real.sqrt (K * c)) := by
        rw [div_le_iff₀ hpos, hKc]
        nlinarith

end OACor

open OACor in
theorem solution {N : ℕ} (T K : ℕ) (hN : 1 ≤ N) (hK : 1 ≤ K) (r v : Fin N → ℝ)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hv : ∀ i, v i ∈ Set.Icc (0 : ℝ) 1)
    (eps epsBar : ℝ) (heps : 0 ≤ eps) (hepsBar : 0 ≤ epsBar)
    (sel : (Fin N → ℝ) → Finset (Fin N) → Fin N → Finset (Fin N)) (hsel : IsArgmaxSel r K sel)
    {t : ℕ} (p : Fin t → Rec N) (τ : ℕ)
    (hsucc : ∀ σ < τ, min 1 (eps * T / (epochLen N K T σ : ℝ)) ≤ 1 / (4 * ((K : ℝ) + 2)) →
      EstimateWithin (⟨T, epsBar, r, K, sel⟩ : Input N) v eps p σ)
    (S : Finset (Fin N)) (hS : S ⊆ (state (⟨T, epsBar, r, K, sel⟩ : Input N) p τ).A)
    (hSK : S.card ≤ K) :
    |rev r (state (⟨T, epsBar, r, K, sel⟩ : Input N) p τ).vhat S - rev r v S| ≤
        deltaHatCorAt (⟨T, epsBar, r, K, sel⟩ : Input N) p eps τ ∧
      |rev r (state (⟨T, epsBar, r, K, sel⟩ : Input N) p τ).vhat S - rev r v S| ≤
        deltaHatCorAt (⟨T, epsBar, r, K, sel⟩ : Input N) p (max eps epsBar) τ := by
  set alg : Input N := ⟨T, epsBar, r, K, sel⟩ with halg
  have hv0 : ∀ i, 0 ≤ v i := fun i => (hv i).1
  have hvhat : ∀ i, 0 ≤ (state alg p τ).vhat i := fun i => (vhat_mem alg p τ i).1
  have hone := abs_rev_sub_le_one r _ v hr hvhat hv0 S
  cases τ with
  | zero => exact ⟨hone, hone⟩
  | succ σ =>
    have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hL : 0 ≤ Real.log (T : ℝ) := Real.log_natCast_nonneg T
    set tl : ℕ := epochLen N K T σ with htl
    set n : ℕ := (state alg p (σ + 1)).A.card with hn
    set L := Real.log (T : ℝ) with hLdef
    have hc0 : 0 ≤ (n : ℝ) * L / tl := by positivity
    -- the main bound, for the true proportion `eps`
    have claim1 : ¬ ((tl : ℝ) < eps * T / (4 * ((K : ℝ) + 1))) →
        |rev r (state alg p (σ + 1)).vhat S - rev r v S| ≤
          16 * K * ((K : ℝ) + 1) *
            (min 1 (eps * T / tl) / 2 + Real.sqrt (min 1 (eps * T / tl) * n * L / tl) +
              2 * n * L / (3 * tl)) +
          max 1 (Real.sqrt ((K : ℝ) + 1) / 2) * (16 * Real.sqrt (K * n * L / tl)) := by
      intro _
      set m := min 1 (eps * T / tl) with hm
      have hm0 : 0 ≤ m := le_min zero_le_one (by positivity)
      have hB0 : 0 ≤ m / 2 + Real.sqrt (m * n * L / tl) + 2 * n * L / (3 * tl) := by
        have := Real.sqrt_nonneg (m * n * L / tl)
        have : 0 ≤ 2 * (n : ℝ) * L / (3 * tl) := by positivity
        linarith [hm0]
      have hsq0 := Real.sqrt_nonneg ((K : ℝ) * n * L / tl)
      by_cases hmc : m ≤ 1 / (4 * ((K : ℝ) + 2))
      · have hE : EstimateWithin alg v eps p σ := hsucc σ (Nat.lt_succ_self σ) hmc
        have hcore := core_bound K r v (state alg p (σ + 1)).vhat hr hv hvhat S hSK
          (m / 2 + Real.sqrt (m * n * L / tl) + 2 * n * L / (3 * tl)) ((n : ℝ) * L / tl) hB0 hc0
          (fun i => ∑ j ∈ sel (state alg p σ).vhat (state alg p σ).A i, v j)
          (fun i hi => by
            have hiA : i ∈ (state alg p σ).A := by
              have := hS hi
              exact (Finset.mem_filter.1 this).1
            refine ⟨Finset.sum_nonneg (fun j _ => hv0 j), ?_⟩
            calc ∑ j ∈ sel (state alg p σ).vhat (state alg p σ).A i, v j
                ≤ ∑ _j ∈ sel (state alg p σ).vhat (state alg p σ).A i, (1 : ℝ) :=
                  Finset.sum_le_sum (fun j _ => (hv j).2)
              _ = ((sel (state alg p σ).vhat (state alg p σ).A i).card : ℝ) := by simp
              _ ≤ K := by exact_mod_cast (hsel _ _ i hiA).2.2.1)
          (fun i hi => by
            have := hE i (hS hi)
            unfold deltaStar at this
            have e : (1 + ∑ j ∈ sel (state alg p σ).vhat (state alg p σ).A i, v j) * v i *
                (n : ℝ) * L / tl =
                (1 + ∑ j ∈ sel (state alg p σ).vhat (state alg p σ).A i, v j) * v i *
                  ((n : ℝ) * L / tl) := by ring
            rw [e] at this
            exact this)
        have e2 : (K : ℝ) * n * L / tl = K * ((n : ℝ) * L / tl) := by ring
        rw [e2]
        have hmax : Real.sqrt ((K : ℝ) + 1) / 2 ≤ max 1 (Real.sqrt ((K : ℝ) + 1) / 2) :=
          le_max_right _ _
        have := mul_le_mul_of_nonneg_right hmax
          (by positivity : (0 : ℝ) ≤ 16 * Real.sqrt (K * ((n : ℝ) * L / tl)))
        linarith
      · push Not at hmc
        have h1 : 1 < 8 * K * ((K : ℝ) + 1) * m := by
          have h4 : 1 < 4 * ((K : ℝ) + 2) * m := by
            rw [div_lt_iff₀ (by positivity)] at hmc; linarith
          have h5 : 4 * ((K : ℝ) + 2) ≤ 8 * K * ((K : ℝ) + 1) := by nlinarith
          nlinarith
        have h2 : 8 * K * ((K : ℝ) + 1) * m ≤ 16 * K * ((K : ℝ) + 1) *
            (m / 2 + Real.sqrt (m * n * L / tl) + 2 * n * L / (3 * tl)) := by
          have : m / 2 ≤ m / 2 + Real.sqrt (m * n * L / tl) + 2 * n * L / (3 * tl) := by
            have := Real.sqrt_nonneg (m * n * L / tl)
            have : 0 ≤ 2 * (n : ℝ) * L / (3 * tl) := by positivity
            linarith
          have hk : 0 ≤ 16 * K * ((K : ℝ) + 1) := by positivity
          nlinarith
        have h3 : 0 ≤ max 1 (Real.sqrt ((K : ℝ) + 1) / 2) * (16 * Real.sqrt (K * n * L / tl)) := by
          have : 0 ≤ max 1 (Real.sqrt ((K : ℝ) + 1) / 2) := le_trans zero_le_one (le_max_left _ _)
          positivity
        linarith
    refine ⟨?_, ?_⟩
    · show _ ≤ deltaHatCor eps T K tl n
      unfold deltaHatCor
      split_ifs with hc
      · exact hone
      · exact claim1 hc
    · show _ ≤ deltaHatCor (max eps epsBar) T K tl n
      unfold deltaHatCor
      split_ifs with hc
      · exact hone
      · have hc1 : ¬ ((tl : ℝ) < eps * T / (4 * ((K : ℝ) + 1))) := by
          intro h
          apply hc
          refine lt_of_lt_of_le h ?_
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        refine (claim1 hc1).trans ?_
        have hmm : min 1 (eps * T / tl) ≤ min 1 (max eps epsBar * T / tl) := by
          apply min_le_min_left
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        have hs : Real.sqrt (min 1 (eps * T / tl) * n * L / tl) ≤
            Real.sqrt (min 1 (max eps epsBar * T / tl) * n * L / tl) := by
          apply Real.sqrt_le_sqrt
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ hL
          exact mul_le_mul_of_nonneg_right hmm (by positivity)
        have hk : 0 ≤ 16 * K * ((K : ℝ) + 1) := by positivity
        have := mul_le_mul_of_nonneg_left (show
          min 1 (eps * T / tl) / 2 + Real.sqrt (min 1 (eps * T / tl) * n * L / tl) +
              2 * n * L / (3 * tl) ≤
            min 1 (max eps epsBar * T / tl) / 2 +
              Real.sqrt (min 1 (max eps epsBar * T / tl) * n * L / tl) + 2 * n * L / (3 * tl) by
          linarith) hk
        linarith
