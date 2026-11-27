-- Prove2me | solution 1 for PerishablePricing.Backlog.Supplement.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:12:10.575039+00:00
-- url     : https://prove2.me/submissions/21ee6fa7-c71c-41ca-b8cc-247639a18dbe

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_Supplement_PositiveShift

open PerishablePricing
open PerishablePricing.Backlog
open PerishablePricing.Backlog.Supplement

/-- Lemma 4 on both carriers allowed by the source. The effective domain is
arbitrary, including empty domains and +∞ values outside it. -/
theorem solution :
    (∀ (n k : ℕ), 1 ≤ k → k ≤ n →
      ∀ (S : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ),
        LNatConvexOn S f → ExtendedMonotoneFirst k S f →
        LNatConvexOn {w ∈ V (n + 1) k | positiveShift k w ∈ S}
          (fun w => f (positiveShift k w))) ∧
    (∀ (n k : ℕ), 1 ≤ k → k ≤ n →
      ∀ (S : Set (Fin n → ℤ)) (f : (Fin n → ℤ) → ℝ),
        LNatConvexOnZ S f → ExtendedMonotoneFirstZ k S f →
        LNatConvexOnZ {w ∈ VZ (n + 1) k | positiveShiftZ k w ∈ S}
          (fun w => f (positiveShiftZ k w))) := by
            refine ⟨?_, ?_⟩
            · intro n k _hk1 _hkn S f hf hmono
              obtain ⟨hS, hfS⟩ := hf
              have hpsiV : ∀ w ∈ V (n+1) k, positiveShift k w ∈ Vplus n k := by
                intro w hw
                refine ⟨?_, ?_⟩
                · intro i j hij hj
                  have hi : (i:ℕ) < k := lt_of_le_of_lt hij hj
                  simp only [positiveShift, hi, hj, if_true]
                  have := hw i.castSucc j.castSucc (Fin.castSucc_le_castSucc_iff.mpr hij) (by simpa using hj)
                  exact max_le_max (by linarith) le_rfl
                · intro i hi
                  simp only [positiveShift, hi, if_true]
                  exact le_max_right _ _
              have core : ∀ (u v a b : Fin (n+1) → ℝ) (γ : ℝ), 0 ≤ γ →
                  u ∈ V (n+1) k → positiveShift k u ∈ S →
                  v ∈ V (n+1) k → positiveShift k v ∈ S →
                  a ∈ V (n+1) k →
                  (∀ i : Fin n, a i.castSucc - a (Fin.last n) =
                    min (u i.castSucc - u (Fin.last n) + γ) (v i.castSucc - v (Fin.last n))) →
                  (∀ i : Fin n, b i.castSucc - b (Fin.last n) =
                    max (u i.castSucc - u (Fin.last n)) (v i.castSucc - v (Fin.last n) - γ)) →
                  positiveShift k a ∈ S ∧ positiveShift k b ∈ S ∧
                    f (positiveShift k a) + f (positiveShift k b) ≤
                      f (positiveShift k u) + f (positiveShift k v) := by
                intro u v a b γ hγ hu huS hv hvS ha hA hB
                have hXp := hpsiV u hu
                have hYp := hpsiV v hv
                obtain ⟨hPS, hQS⟩ := hS _ huS _ hvS γ hγ
                have hineq := hfS _ huS _ hvS γ hγ
                have hQ : positiveShift k b = positiveShift k u ⊔ (positiveShift k v - γ • (1 : Fin n → ℝ)) := by
                  funext i
                  simp only [Pi.sup_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
                    positiveShift]
                  rw [hB i]
                  split_ifs with hi
                  · simp only [max_def, min_def]; split_ifs <;> linarith
                  · rfl
                have hPp : (positiveShift k u + γ • (1 : Fin n → ℝ)) ⊓ positiveShift k v ∈ Vplus n k := by
                  refine ⟨?_, ?_⟩
                  · intro i j hij hj
                    have h1 := hXp.1 i j hij hj
                    have h2 := hYp.1 i j hij hj
                    simp only [Pi.inf_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
                    exact inf_le_inf (by linarith) h2
                  · intro i hi
                    have h1 := hXp.2 i hi
                    have h2 := hYp.2 i hi
                    simp only [Pi.inf_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
                    exact le_inf (by linarith) h2
                have hle : ∀ i : Fin n, (i:ℕ) < k → positiveShift k a i ≤
                    ((positiveShift k u + γ • (1 : Fin n → ℝ)) ⊓ positiveShift k v) i := by
                  intro i hi
                  simp only [Pi.inf_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
                    positiveShift, hi, if_true]
                  rw [hA i]
                  simp only [max_def, min_def]; split_ifs <;> linarith
                have heq : ∀ i : Fin n, k ≤ (i:ℕ) → positiveShift k a i =
                    ((positiveShift k u + γ • (1 : Fin n → ℝ)) ⊓ positiveShift k v) i := by
                  intro i hi
                  have hi' : ¬ (i:ℕ) < k := not_lt.mpr hi
                  simp only [Pi.inf_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
                    positiveShift, hi', if_false]
                  rw [hA i]
                obtain ⟨haS, hfa⟩ := hmono _ (hpsiV a ha) _ hPp hle heq hPS
                refine ⟨haS, hQ ▸ hQS, ?_⟩
                rw [hQ]; linarith
              have hVlat : ∀ u ∈ V (n+1) k, ∀ v ∈ V (n+1) k, ∀ α : ℝ, 0 ≤ α →
                  (u + α • (1 : Fin (n+1) → ℝ)) ⊓ v ∈ V (n+1) k ∧
                    u ⊔ (v - α • (1 : Fin (n+1) → ℝ)) ∈ V (n+1) k := by
                intro u hu v hv α _hα
                refine ⟨?_, ?_⟩
                · intro i j hij hj
                  have h1 := hu i j hij hj
                  have h2 := hv i j hij hj
                  simp only [Pi.inf_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
                  exact inf_le_inf (by linarith) h2
                · intro i j hij hj
                  have h1 := hu i j hij hj
                  have h2 := hv i j hij hj
                  simp only [Pi.sup_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
                  exact sup_le_sup h1 (by linarith)
              have main : ∀ u ∈ {w ∈ V (n + 1) k | positiveShift k w ∈ S},
                  ∀ v ∈ {w ∈ V (n + 1) k | positiveShift k w ∈ S}, ∀ α : ℝ, 0 ≤ α →
                  ((u + α • (1 : Fin (n+1) → ℝ)) ⊓ v ∈ {w ∈ V (n + 1) k | positiveShift k w ∈ S} ∧
                    u ⊔ (v - α • (1 : Fin (n+1) → ℝ)) ∈ {w ∈ V (n + 1) k | positiveShift k w ∈ S}) ∧
                  f (positiveShift k ((u + α • (1 : Fin (n+1) → ℝ)) ⊓ v)) +
                    f (positiveShift k (u ⊔ (v - α • (1 : Fin (n+1) → ℝ)))) ≤
                      f (positiveShift k u) + f (positiveShift k v) := by
                intro u hu v hv α hα
                obtain ⟨huV, huS⟩ := hu
                obtain ⟨hvV, hvS⟩ := hv
                obtain ⟨haV, hbV⟩ := hVlat u huV v hvV α hα
                rcases le_total (v (Fin.last n)) (u (Fin.last n) + α) with h | h
                · obtain ⟨h1, h2, h3⟩ := core u v ((u + α • (1 : Fin (n+1) → ℝ)) ⊓ v)
                    (u ⊔ (v - α • (1 : Fin (n+1) → ℝ))) (u (Fin.last n) + α - v (Fin.last n))
                    (by linarith) huV huS hvV hvS haV
                    (fun i => by
                      simp only [Pi.inf_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
                      simp only [min_def]; split_ifs <;> linarith)
                    (fun i => by
                      simp only [Pi.sup_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
                      simp only [max_def]; split_ifs <;> linarith)
                  exact ⟨⟨⟨haV, h1⟩, ⟨hbV, h2⟩⟩, h3⟩
                · obtain ⟨h1, h2, h3⟩ := core v u ((u + α • (1 : Fin (n+1) → ℝ)) ⊓ v)
                    (u ⊔ (v - α • (1 : Fin (n+1) → ℝ))) (v (Fin.last n) - u (Fin.last n) - α)
                    (by linarith) hvV hvS huV huS haV
                    (fun i => by
                      simp only [Pi.inf_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
                      simp only [min_def]; split_ifs <;> linarith)
                    (fun i => by
                      simp only [Pi.sup_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
                      simp only [max_def]; split_ifs <;> linarith)
                  exact ⟨⟨⟨haV, h1⟩, ⟨hbV, h2⟩⟩, by linarith⟩
              exact ⟨fun u hu v hv α hα => (main u hu v hv α hα).1,
                fun u hu v hv α hα => (main u hu v hv α hα).2⟩
            · intro n k _hk1 _hkn S f hf hmono
              obtain ⟨hS, hfS⟩ := hf
              have hpsiV : ∀ w ∈ VZ (n+1) k, positiveShiftZ k w ∈ VplusZ n k := by
                intro w hw
                refine ⟨?_, ?_⟩
                · intro i j hij hj
                  have hi : (i:ℕ) < k := lt_of_le_of_lt hij hj
                  simp only [positiveShiftZ, hi, hj, if_true]
                  have := hw i.castSucc j.castSucc (Fin.castSucc_le_castSucc_iff.mpr hij) (by simpa using hj)
                  exact max_le_max (by linarith) le_rfl
                · intro i hi
                  simp only [positiveShiftZ, hi, if_true]
                  exact le_max_right _ _
              have core : ∀ (u v a b : Fin (n+1) → ℤ) (γ : ℤ), 0 ≤ γ →
                  u ∈ VZ (n+1) k → positiveShiftZ k u ∈ S →
                  v ∈ VZ (n+1) k → positiveShiftZ k v ∈ S →
                  a ∈ VZ (n+1) k →
                  (∀ i : Fin n, a i.castSucc - a (Fin.last n) =
                    min (u i.castSucc - u (Fin.last n) + γ) (v i.castSucc - v (Fin.last n))) →
                  (∀ i : Fin n, b i.castSucc - b (Fin.last n) =
                    max (u i.castSucc - u (Fin.last n)) (v i.castSucc - v (Fin.last n) - γ)) →
                  positiveShiftZ k a ∈ S ∧ positiveShiftZ k b ∈ S ∧
                    f (positiveShiftZ k a) + f (positiveShiftZ k b) ≤
                      f (positiveShiftZ k u) + f (positiveShiftZ k v) := by
                intro u v a b γ hγ hu huS hv hvS ha hA hB
                have hXp := hpsiV u hu
                have hYp := hpsiV v hv
                obtain ⟨hPS, hQS⟩ := hS _ huS _ hvS γ hγ
                have hineq := hfS _ huS _ hvS γ hγ
                have hQ : positiveShiftZ k b = positiveShiftZ k u ⊔ (positiveShiftZ k v - γ • (1 : Fin n → ℤ)) := by
                  funext i
                  simp only [Pi.sup_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
                    positiveShiftZ]
                  rw [hB i]
                  split_ifs with hi
                  · simp only [max_def, min_def]; split_ifs <;> linarith
                  · rfl
                have hPp : (positiveShiftZ k u + γ • (1 : Fin n → ℤ)) ⊓ positiveShiftZ k v ∈ VplusZ n k := by
                  refine ⟨?_, ?_⟩
                  · intro i j hij hj
                    have h1 := hXp.1 i j hij hj
                    have h2 := hYp.1 i j hij hj
                    simp only [Pi.inf_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
                    exact inf_le_inf (by linarith) h2
                  · intro i hi
                    have h1 := hXp.2 i hi
                    have h2 := hYp.2 i hi
                    simp only [Pi.inf_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
                    exact le_inf (by linarith) h2
                have hle : ∀ i : Fin n, (i:ℕ) < k → positiveShiftZ k a i ≤
                    ((positiveShiftZ k u + γ • (1 : Fin n → ℤ)) ⊓ positiveShiftZ k v) i := by
                  intro i hi
                  simp only [Pi.inf_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
                    positiveShiftZ, hi, if_true]
                  rw [hA i]
                  simp only [max_def, min_def]; split_ifs <;> linarith
                have heq : ∀ i : Fin n, k ≤ (i:ℕ) → positiveShiftZ k a i =
                    ((positiveShiftZ k u + γ • (1 : Fin n → ℤ)) ⊓ positiveShiftZ k v) i := by
                  intro i hi
                  have hi' : ¬ (i:ℕ) < k := not_lt.mpr hi
                  simp only [Pi.inf_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
                    positiveShiftZ, hi', if_false]
                  rw [hA i]
                obtain ⟨haS, hfa⟩ := hmono _ (hpsiV a ha) _ hPp hle heq hPS
                refine ⟨haS, hQ ▸ hQS, ?_⟩
                rw [hQ]; linarith
              have hVlat : ∀ u ∈ VZ (n+1) k, ∀ v ∈ VZ (n+1) k, ∀ α : ℤ, 0 ≤ α →
                  (u + α • (1 : Fin (n+1) → ℤ)) ⊓ v ∈ VZ (n+1) k ∧
                    u ⊔ (v - α • (1 : Fin (n+1) → ℤ)) ∈ VZ (n+1) k := by
                intro u hu v hv α _hα
                refine ⟨?_, ?_⟩
                · intro i j hij hj
                  have h1 := hu i j hij hj
                  have h2 := hv i j hij hj
                  simp only [Pi.inf_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
                  exact inf_le_inf (by linarith) h2
                · intro i j hij hj
                  have h1 := hu i j hij hj
                  have h2 := hv i j hij hj
                  simp only [Pi.sup_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
                  exact sup_le_sup h1 (by linarith)
              have main : ∀ u ∈ {w ∈ VZ (n + 1) k | positiveShiftZ k w ∈ S},
                  ∀ v ∈ {w ∈ VZ (n + 1) k | positiveShiftZ k w ∈ S}, ∀ α : ℤ, 0 ≤ α →
                  ((u + α • (1 : Fin (n+1) → ℤ)) ⊓ v ∈ {w ∈ VZ (n + 1) k | positiveShiftZ k w ∈ S} ∧
                    u ⊔ (v - α • (1 : Fin (n+1) → ℤ)) ∈ {w ∈ VZ (n + 1) k | positiveShiftZ k w ∈ S}) ∧
                  f (positiveShiftZ k ((u + α • (1 : Fin (n+1) → ℤ)) ⊓ v)) +
                    f (positiveShiftZ k (u ⊔ (v - α • (1 : Fin (n+1) → ℤ)))) ≤
                      f (positiveShiftZ k u) + f (positiveShiftZ k v) := by
                intro u hu v hv α hα
                obtain ⟨huV, huS⟩ := hu
                obtain ⟨hvV, hvS⟩ := hv
                obtain ⟨haV, hbV⟩ := hVlat u huV v hvV α hα
                rcases le_total (v (Fin.last n)) (u (Fin.last n) + α) with h | h
                · obtain ⟨h1, h2, h3⟩ := core u v ((u + α • (1 : Fin (n+1) → ℤ)) ⊓ v)
                    (u ⊔ (v - α • (1 : Fin (n+1) → ℤ))) (u (Fin.last n) + α - v (Fin.last n))
                    (by linarith) huV huS hvV hvS haV
                    (fun i => by
                      simp only [Pi.inf_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
                      simp only [min_def]; split_ifs <;> linarith)
                    (fun i => by
                      simp only [Pi.sup_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
                      simp only [max_def]; split_ifs <;> linarith)
                  exact ⟨⟨⟨haV, h1⟩, ⟨hbV, h2⟩⟩, h3⟩
                · obtain ⟨h1, h2, h3⟩ := core v u ((u + α • (1 : Fin (n+1) → ℤ)) ⊓ v)
                    (u ⊔ (v - α • (1 : Fin (n+1) → ℤ))) (v (Fin.last n) - u (Fin.last n) - α)
                    (by linarith) hvV hvS huV huS haV
                    (fun i => by
                      simp only [Pi.inf_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
                      simp only [min_def]; split_ifs <;> linarith)
                    (fun i => by
                      simp only [Pi.sup_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
                      simp only [max_def]; split_ifs <;> linarith)
                  exact ⟨⟨⟨haV, h1⟩, ⟨hbV, h2⟩⟩, by linarith⟩
              exact ⟨fun u hu v hv α hα => (main u hu v hv α hα).1,
                fun u hu v hv α hα => (main u hu v hv α hα).2⟩
