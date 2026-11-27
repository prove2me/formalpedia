-- Prove2me | solution 1 for OfflinePolicyLearning.Trees.Supplement.theorem1_printed_equality_false
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:33:52.384008+00:00
-- url     : https://prove2.me/submissions/5b8415f3-3cba-41be-8549-09bc3a043f6d

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming
import Definitions.Def_OfflinePolicyLearning_Trees_Supplement_Setting

open MeasureTheory Filter Topology

open OfflinePolicyLearning
open OfflinePolicyLearning.Trees
open OfflinePolicyLearning.Trees.Supplement

/-- Theorem 1 (6), p. 16, as printed — `ℛₙ(Πᴰ) = 27.2√2(κ(Π) + 8)√(V*/n) + o(1/√n)` for iid
bounded feature–score pairs under Assumption 3 — is false. Its negation is stated already for
nonempty finite classes of measurable policies (a special case of the printed hypotheses). -/
theorem solution :
    ¬ ∀ (X : Type) [MeasurableSpace X] (d : ℕ) (P : Measure (X × (Fin d → ℝ)))
        [IsProbabilityMeasure P] (Pol : Set (X → Fin d)),
        Pol.Nonempty → Pol.Finite → (∀ π ∈ Pol, Measurable π) →
        (∃ B : ℝ, ∀ᵐ z ∂P, ∀ j, |z.2 j| ≤ B) →
        (∃ C D ω : ℝ, 0 < C ∧ 0 < D ∧ 0 < ω ∧ ω < 1 / 2 ∧
          ∀ ε : ℝ, 0 < ε → ε < 1 →
            OfflinePolicyLearning.Regret.hammingCoverNum ε Pol ≠ ⊤ ∧
            ((OfflinePolicyLearning.Regret.hammingCoverNum ε Pol).toNat : ℝ) ≤
              C * Real.exp (D * (1 / ε) ^ ω)) →
        Tendsto (fun n : ℕ => Real.sqrt n * (policyDiffRademacher P n Pol -
            27.2 * Real.sqrt 2 * ((OfflinePolicyLearning.Regret.entropyIntegral Pol).toReal + 8) *
              Real.sqrt (scoreVstar P Pol / n)))
          atTop (𝓝 0) := by
            intro h
            let p : Unit × (Fin 2 → ℝ) := ((), fun j => (j.val : ℝ))
            let Pol : Set (Unit → Fin 2) := {fun _ => 0, fun _ => 1}
            have hPolfin : Pol.Finite := Set.toFinite _
            have hcov : ∀ ε : ℝ, 0 ≤ ε → OfflinePolicyLearning.Regret.hammingCoverNum ε Pol ≤ 2 := by
              intro ε hε
              unfold OfflinePolicyLearning.Regret.hammingCoverNum
              refine iSup₂_le fun m _ => iSup_le fun x => ?_
              have : OfflinePolicyLearning.Regret.hammingCoverNumOn ε Pol x ≤ 2 := by
                apply Nat.sInf_le
                refine ⟨![fun _ => 0, fun _ => 1], ?_, ?_⟩
                · intro i; fin_cases i <;> simp [Pol]
                · intro π hπ
                  rcases hπ with rfl | rfl
                  · exact ⟨0, by simp [OfflinePolicyLearning.Regret.hammingDist, hε]⟩
                  · exact ⟨1, by simp [OfflinePolicyLearning.Regret.hammingDist, hε]⟩
              exact_mod_cast this
            have key := h Unit 2 (Measure.dirac p) Pol ⟨_, Set.mem_insert _ _⟩ hPolfin
              (fun π _ => Subsingleton.measurable)
              ⟨1, by
                rw [ae_dirac_eq]
                refine Filter.eventually_pure.2 ?_
                intro j; fin_cases j <;> simp [p]⟩
              ⟨2, 1, 1/4, by norm_num, by norm_num, by norm_num, by norm_num, by
                intro ε hε _
                have h2 := hcov ε hε.le
                have hne : OfflinePolicyLearning.Regret.hammingCoverNum ε Pol ≠ ⊤ :=
                  ne_top_of_le_ne_top (by decide) h2
                refine ⟨hne, ?_⟩
                have h3 : (OfflinePolicyLearning.Regret.hammingCoverNum ε Pol).toNat ≤ 2 := by
                  have := ENat.toNat_le_toNat h2 (by decide)
                  simpa using this
                have h4 : (1 : ℝ) ≤ Real.exp (1 * (1 / ε) ^ (1/4 : ℝ)) := Real.one_le_exp (by positivity)
                have h5 : ((OfflinePolicyLearning.Regret.hammingCoverNum ε Pol).toNat : ℝ) ≤ 2 := by
                  exact_mod_cast h3
                linarith⟩
            -- sum of squares of sign sums
            have hsq : ∀ n : ℕ, ∑ σ : Fin n → Bool, (∑ i, (if σ i then (1:ℝ) else -1)) ^ 2
                = 2 ^ n * n := by
              intro n
              have hpair : ∀ i j : Fin n, ∑ σ : Fin n → Bool,
                  (if σ i then (1:ℝ) else -1) * (if σ j then (1:ℝ) else -1)
                    = if i = j then 2 ^ n else 0 := by
                intro i j
                by_cases hij : i = j
                · subst hij
                  simp only [if_true]
                  have : ∀ σ : Fin n → Bool, (if σ i then (1:ℝ) else -1) * (if σ i then (1:ℝ) else -1) = 1 := by
                    intro σ; cases σ i <;> norm_num
                  simp [this]
                · rw [if_neg hij]
                  let e : (Fin n → Bool) ≃ (Fin n → Bool) :=
                    { toFun := fun σ => Function.update σ i (!(σ i))
                      invFun := fun σ => Function.update σ i (!(σ i))
                      left_inv := fun σ => by ext k; by_cases hk : k = i <;> simp [Function.update, hk]
                      right_inv := fun σ => by ext k; by_cases hk : k = i <;> simp [Function.update, hk] }
                  have hflip := Equiv.sum_comp e (fun σ : Fin n → Bool =>
                    (if σ i then (1:ℝ) else -1) * (if σ j then (1:ℝ) else -1))
                  have hval : ∀ σ : Fin n → Bool,
                      (if (e σ) i then (1:ℝ) else -1) * (if (e σ) j then (1:ℝ) else -1)
                        = -((if σ i then (1:ℝ) else -1) * (if σ j then (1:ℝ) else -1)) := by
                    intro σ
                    have h1 : (e σ) i = !(σ i) := by simp [e]
                    have h2 : (e σ) j = σ j := by simp [e, Function.update, Ne.symm hij]
                    rw [h1, h2]; cases σ i <;> cases σ j <;> norm_num
                  simp only [hval, Finset.sum_neg_distrib] at hflip
                  linarith
              calc ∑ σ : Fin n → Bool, (∑ i, (if σ i then (1:ℝ) else -1)) ^ 2
                  = ∑ σ : Fin n → Bool, ∑ i, ∑ j,
                      (if σ i then (1:ℝ) else -1) * (if σ j then (1:ℝ) else -1) := by
                    refine Finset.sum_congr rfl fun σ _ => ?_
                    rw [sq, Finset.sum_mul_sum]
                _ = ∑ i, ∑ j, ∑ σ : Fin n → Bool,
                      (if σ i then (1:ℝ) else -1) * (if σ j then (1:ℝ) else -1) := by
                    rw [Finset.sum_comm]
                    refine Finset.sum_congr rfl fun i _ => ?_
                    rw [Finset.sum_comm]
                _ = 2 ^ n * n := by
                    simp only [hpair, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
                      Finset.card_univ, Fintype.card_fin]
                    simp; ring
            have habs : ∀ n : ℕ, 0 < n → ∑ σ : Fin n → Bool, |∑ i, (if σ i then (1:ℝ) else -1)|
                ≤ 2 ^ n * Real.sqrt n := by
              intro n hn
              have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
              have hss : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by positivity)
              have hpt : ∀ σ : Fin n → Bool, 2 * Real.sqrt n * |∑ i, (if σ i then (1:ℝ) else -1)|
                  ≤ (∑ i, (if σ i then (1:ℝ) else -1)) ^ 2 + n := by
                intro σ
                have := sq_nonneg (|∑ i, (if σ i then (1:ℝ) else -1)| - Real.sqrt n)
                rw [sub_sq, sq_abs] at this
                nlinarith
              have hsum := Finset.sum_le_sum (fun σ (_ : σ ∈ Finset.univ) => hpt σ)
              rw [← Finset.mul_sum, Finset.sum_add_distrib, hsq] at hsum
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
                Fintype.card_fin, nsmul_eq_mul] at hsum
              push_cast at hsum
              have h2n : (0:ℝ) < 2 ^ n := by positivity
              nlinarith
            have hpi : ∀ n : ℕ, (Measure.pi fun _ : Fin n => Measure.dirac p) = Measure.dirac (fun _ => p) := by
              intro n
              refine Measure.pi_eq (μ' := Measure.dirac (fun _ : Fin n => p)) fun s hs => ?_
              rw [Measure.dirac_apply]
              by_cases hall : ∀ i, p ∈ s i
              · have hm : (fun _ : Fin n => p) ∈ Set.univ.pi s := fun i _ => hall i
                rw [Set.indicator_of_mem hm]
                simp [Measure.dirac_apply, hall]
              · push Not at hall
                obtain ⟨i, hi⟩ := hall
                have hm : (fun _ : Fin n => p) ∉ Set.univ.pi s := fun hh => hi (hh i trivial)
                rw [Set.indicator_of_notMem hm]
                symm
                refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
                simp [Measure.dirac_apply, hi]
            have hR : ∀ n : ℕ, 0 < n → Real.sqrt n * policyDiffRademacher (Measure.dirac p) n Pol ≤ 1 := by
              intro n hn
              unfold policyDiffRademacher DRBatchBandit.rademacher
              rw [hpi, integral_dirac]
              have hne : Nonempty (policyDiffClass Pol) :=
                ⟨⟨fun z => z.2 ((fun _ => 0 : Unit → Fin 2) z.1) - z.2 ((fun _ => 0 : Unit → Fin 2) z.1),
                  _, Set.mem_insert _ _, _, Set.mem_insert _ _, rfl⟩⟩
              have hfb : ∀ f : policyDiffClass Pol, |f.1 p| ≤ 1 := by
                rintro ⟨f, πa, hπa, πb, hπb, rfl⟩
                rcases hπa with rfl | rfl <;> rcases hπb with rfl | rfl <;> norm_num [p]
              have hsup : ∀ σ : Fin n → Bool,
                  (⨆ f : policyDiffClass Pol, |(1 / n : ℝ) * ∑ i, (if σ i then (1 : ℝ) else -1) * f.1 p|)
                    ≤ (1 / n : ℝ) * |∑ i, (if σ i then (1:ℝ) else -1)| := by
                intro σ
                refine ciSup_le fun f => ?_
                rw [← Finset.sum_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / n)]
                have := hfb f
                have h0 : 0 ≤ |∑ i, (if σ i then (1:ℝ) else -1)| := abs_nonneg _
                have h1 : (0:ℝ) < 1 / n := by positivity
                calc 1 / (n:ℝ) * (|∑ i, (if σ i then (1:ℝ) else -1)| * |f.1 p|)
                    ≤ 1 / (n:ℝ) * (|∑ i, (if σ i then (1:ℝ) else -1)| * 1) := by gcongr
                  _ = _ := by ring
              have hS := Finset.sum_le_sum (fun σ (_ : σ ∈ Finset.univ) => hsup σ)
              rw [← Finset.mul_sum] at hS
              have hA := habs n hn
              have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
              have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (by positivity)
              have h2n : (0:ℝ) < 2 ^ n := by positivity
              have hnpos : (0:ℝ) < n := by exact_mod_cast hn
              set T := ∑ σ : Fin n → Bool,
                  ⨆ f : policyDiffClass Pol, |(1 / n : ℝ) * ∑ i, (if σ i then (1 : ℝ) else -1) * f.1 p|
              set A := ∑ σ : Fin n → Bool, |∑ i, (if σ i then (1:ℝ) else -1)|
              have hT : T ≤ 2 ^ n * Real.sqrt n / n := by
                calc T ≤ 1 / n * A := hS
                  _ ≤ 1 / n * (2 ^ n * Real.sqrt n) := by gcongr
                  _ = _ := by ring
              calc Real.sqrt n * (1 / 2 ^ n * T) ≤ Real.sqrt n * (1 / 2 ^ n * (2 ^ n * Real.sqrt n / n)) := by
                    gcongr
                _ = 1 := by field_simp; linarith
            have hV : 1 ≤ scoreVstar (Measure.dirac p) Pol := by
              unfold scoreVstar
              have h1 : (fun _ => 1 : Unit → Fin 2) ∈ Pol := Set.mem_insert_of_mem _ rfl
              have h0 : (fun _ => 0 : Unit → Fin 2) ∈ Pol := Set.mem_insert _ _
              have : Finite Pol := hPolfin.to_subtype
              refine le_ciSup_of_le (Finite.bddAbove_range _) ⟨_, h1⟩ ?_
              refine le_ciSup_of_le (Finite.bddAbove_range _) ⟨_, h0⟩ ?_
              rw [integral_dirac]
              norm_num [p]
            obtain ⟨n, hn1, hn2⟩ := ((key.eventually (Ioo_mem_nhds (by norm_num : (-1:ℝ) < 0)
              (by norm_num : (0:ℝ) < 1))).and (eventually_ge_atTop 1)).exists
            have hn : 0 < n := hn2
            have hRn := hR n hn
            have hnpos : (0:ℝ) < n := by exact_mod_cast hn
            have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
            have ha : 1 ≤ Real.sqrt n * Real.sqrt (scoreVstar (Measure.dirac p) Pol / n) := by
              rw [← Real.sqrt_mul hnpos.le, mul_div_cancel₀ _ hnpos.ne']
              exact Real.one_le_sqrt.2 hV
            have hκ : 0 ≤ (OfflinePolicyLearning.Regret.entropyIntegral Pol).toReal := ENNReal.toReal_nonneg
            have h2 : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.2 (by norm_num)
            have hK : 200 ≤ 27.2 * Real.sqrt 2 *
                ((OfflinePolicyLearning.Regret.entropyIntegral Pol).toReal + 8) := by nlinarith
            have hlow := hn1.1
            set K := 27.2 * Real.sqrt 2 *
                ((OfflinePolicyLearning.Regret.entropyIntegral Pol).toReal + 8)
            set a := Real.sqrt n * Real.sqrt (scoreVstar (Measure.dirac p) Pol / n)
            have : Real.sqrt n * (policyDiffRademacher (Measure.dirac p) n Pol -
                K * Real.sqrt (scoreVstar (Measure.dirac p) Pol / n)) =
                Real.sqrt n * policyDiffRademacher (Measure.dirac p) n Pol - K * a := by
              simp only [a]; ring
            rw [this] at hlow
            nlinarith
