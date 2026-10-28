-- Prove2me | solution 1 for ThresholdTheorem.level_k_concatenated_simulation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T20:33:25.316991+00:00
-- url     : https://prove2.me/submissions/6dcac6fb-eecd-4e4f-809f-4816c1b3bc16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_threshold_theorem_noise_model
import Definitions.Def_threshold_theorem_local_stochastic
import Theorems.Thm_ThresholdTheorem_level_one_local_stochastic_reduction
import Theorems.Thm_ThresholdTheorem_localStochastic_tvDist_le
import Theorems.Thm_ThresholdTheorem_noiseModel_isLocalStochastic
import Theorems.Thm_ThresholdTheorem_isLocalStochastic_relabel

open ThresholdTheorem

theorem levelk_pushDist_pushDist {α β γ : Type*} [Fintype α] [Fintype β] (f : α → β) (g : β → γ)
    (P : α → ℝ) : pushDist g (pushDist f P) = pushDist (g ∘ f) P := by
  classical
  funext z
  simp only [pushDist]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun x => (g ∘ f) x = z))
    (t := Finset.univ.filter (fun y => g y = z)) (g := f)]
  · refine Finset.sum_congr rfl fun y hy => ?_
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at hy ⊢
    constructor
    · intro h; exact ⟨by rw [h, hy], h⟩
    · intro h; exact h.2
  · intro x hx
    simpa using hx

theorem levelk_circuit_relabel_size {Q Q' : Type*} [DecidableEq Q] [DecidableEq Q'] (σ : Q ≃ Q')
    (C : Circuit Q) : (C.relabel σ).size = C.size := by
  simp [Circuit.size, Circuit.relabel, Layer.relabel, Function.comp_def]

theorem solution :
    ∃ (c A : ℝ) (d : ℕ), 0 < c ∧ ∀ k : ℕ, ∃ (b : ℕ) (dec : (Fin b → Fin 2) → Fin 2),
      ∀ (n : ℕ) (C : Circuit (Fin n)), ∃ C' : Circuit (Fin n × Fin b),
        (C'.size : ℝ) ≤ A * (d : ℝ) ^ k * C.size ∧
        ∀ (p : ℝ), 0 ≤ p → c * p < 1 → ∀ N : NoiseModel p,
          tvDist (decodeDist dec (outDist (noisyState N C'))) (outDist (idealState C))
            ≤ (c * p) ^ (2 ^ k) / c * C.size := by
  obtain ⟨c, A₁, b₁, dec₁, hc, hA⟩ := level_one_local_stochastic_reduction
  have hc0 : 0 < c := by linarith
  have hAd : A₁ ≤ (⌈A₁⌉₊ : ℝ) := Nat.le_ceil A₁
  have hd0 : (0 : ℝ) ≤ (⌈A₁⌉₊ : ℝ) := Nat.cast_nonneg _
  have key : ∀ k : ℕ, ∃ (bk : ℕ) (deck : (Fin bk → Fin 2) → Fin 2),
      ∀ (Q : Type) [Fintype Q] [DecidableEq Q] (C : Circuit Q), ∃ C' : Circuit (Q × Fin bk),
        (C'.size : ℝ) ≤ (⌈A₁⌉₊ : ℝ) ^ k * C.size ∧
        ∀ e : ℝ, 0 ≤ e → ∀ P : (Q × Fin bk → Fin 2) → ℝ, IsLocalStochasticDist C' e P →
          tvDist (pushDist (blockMap deck) P) (outDist (idealState C))
            ≤ (c * e) ^ (2 ^ k) / c * C.size := by
    intro k
    induction k with
    | zero =>
      refine ⟨1, fun x => x 0, ?_⟩
      intro Q _ _ C
      refine ⟨C.relabel (Equiv.prodUnique Q (Fin 1)).symm, ?_, ?_⟩
      · simp [levelk_circuit_relabel_size]
      · intro e he P hP
        have h1 := isLocalStochastic_relabel _ C e P hP
        have h2 := localStochastic_tvDist_le C e he _ h1
        have hmap : (blockMap (fun x : Fin 1 → Fin 2 => x 0) : (Q × Fin 1 → Fin 2) → Q → Fin 2)
            = fun x => x ∘ (Equiv.prodUnique Q (Fin 1)).symm := by
          funext x q
          rfl
        rw [hmap]
        refine h2.trans (le_of_eq ?_)
        field_simp
        ring
    | succ k ih =>
      obtain ⟨bk, deck, hk⟩ := ih
      refine ⟨bk * b₁, fun y => deck (fun j => dec₁ (fun l => y (finProdFinEquiv (j, l)))), ?_⟩
      intro Q _ _ C
      obtain ⟨Ck, hsk, hek⟩ := hk Q C
      obtain ⟨C1, hs1, he1⟩ := hA (Q × Fin bk) Ck
      let σ : (Q × Fin bk) × Fin b₁ ≃ Q × Fin (bk * b₁) :=
        (Equiv.prodAssoc Q (Fin bk) (Fin b₁)).trans
          (Equiv.prodCongr (Equiv.refl Q) finProdFinEquiv)
      refine ⟨C1.relabel σ, ?_, ?_⟩
      · rw [levelk_circuit_relabel_size]
        have hCk0 : (0 : ℝ) ≤ Ck.size := Nat.cast_nonneg _
        calc (C1.size : ℝ) ≤ A₁ * Ck.size := hs1
          _ ≤ (⌈A₁⌉₊ : ℝ) * Ck.size := mul_le_mul_of_nonneg_right hAd hCk0
          _ ≤ (⌈A₁⌉₊ : ℝ) * ((⌈A₁⌉₊ : ℝ) ^ k * C.size) := mul_le_mul_of_nonneg_left hsk hd0
          _ = (⌈A₁⌉₊ : ℝ) ^ (k + 1) * C.size := by ring
      · intro e he P hP
        have h1 := isLocalStochastic_relabel σ C1 e P hP
        have h2 := he1 e he _ h1
        have h3 := hek (c * e ^ 2) (by positivity) _ h2
        rw [levelk_pushDist_pushDist, levelk_pushDist_pushDist] at h3
        have hmap : ((blockMap deck ∘ blockMap dec₁) ∘ fun x => x ∘ σ) =
            blockMap (fun y : Fin (bk * b₁) → Fin 2 =>
              deck (fun j => dec₁ (fun l => y (finProdFinEquiv (j, l))))) := by
          funext x q
          rfl
        rw [hmap] at h3
        have hpow : (c * (c * e ^ 2)) ^ 2 ^ k = (c * e) ^ 2 ^ (k + 1) := by
          rw [pow_succ' (2:ℕ) k, pow_mul]
          ring
        rw [hpow] at h3
        exact h3
  refine ⟨c, 1, ⌈A₁⌉₊, hc0, fun k => ?_⟩
  obtain ⟨bk, deck, hk⟩ := key k
  refine ⟨bk, deck, fun n C => ?_⟩
  obtain ⟨C', hs, he⟩ := hk (Fin n) C
  refine ⟨C', by simpa using hs, fun p hp hcp N => ?_⟩
  have hp1 : p ≤ 1 := by nlinarith
  have h := he p hp _ (noiseModel_isLocalStochastic C' p hp hp1 N)
  refine le_of_eq_of_le ?_ h
  congr 1
  funext y
  simp only [decodeDist, pushDist]
  congr


