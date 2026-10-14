-- Prove2me | solution 1 for SoysterInexactLP.Auxiliary.theorem_lp_feasible_iff
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T01:55:52.509102+00:00
-- url     : https://prove2.me/submissions/65d4a0eb-712d-4324-884b-07792ad60850

import Mathlib
import Definitions.Def_SoysterInexactLP_Auxiliary_Problems
open Pointwise Matrix
open SoysterInexactLP.Auxiliary

private theorem choice_iff {m n : ℕ} (K : Fin n → Set (Fin m → ℝ))
    (R : Set (Fin m → ℝ)) (x : Fin n → ℝ) :
    FeasibleI K R x ↔ (∀ j, 0 ≤ x j) ∧
      ∀ a : Fin n → Fin m → ℝ, (∀ j, a j ∈ K j) → ∑ j, x j • a j ∈ R := by
  classical
  constructor
  · rintro ⟨hx, hR⟩
    refine ⟨hx, fun a ha => hR ?_⟩
    exact (Set.mem_fintype_sum _ _).mpr
      ⟨fun j => x j • a j, fun j => Set.smul_mem_smul_set (ha j), rfl⟩
  · rintro ⟨hx, hR⟩
    refine ⟨hx, fun y hy => ?_⟩
    obtain ⟨z, hz, rfl⟩ := (Set.mem_fintype_sum _ _).mp hy
    choose a ha heq using fun j => Set.mem_smul_set.mp (hz j)
    have hfun : z = fun j => x j • a j := by
      funext j
      exact (heq j).symm
    rw [hfun]
    exact hR a ha

private theorem coordinate_support {m : ℕ} (K : Set (Fin m → ℝ)) (i : Fin m) :
    supportFun K (Pi.single i 1) = ⨆ a ∈ K, (a i : EReal) := by
  simp [supportFun, dotProduct, Pi.single_apply]

private theorem coordinate_le {m : ℕ} (K : Set (Fin m → ℝ))
    (i : Fin m) {a : Fin m → ℝ} (ha : a ∈ K) :
    (a i : EReal) ≤ supportFun K (Pi.single i 1) := by
  rw [coordinate_support]
  exact le_iSup_of_le a (le_iSup_of_le ha le_rfl)

private theorem support_not_bot {m : ℕ} (K : Set (Fin m → ℝ))
    (hne : K.Nonempty) (i : Fin m) : supportFun K (Pi.single i 1) ≠ ⊥ := by
  obtain ⟨a, ha⟩ := hne
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (coordinate_le K i ha)

private theorem entry_le {m n : ℕ} (K : Fin n → Set (Fin m → ℝ))
    (hfin : ∀ i j, supportFun (K j) (Pi.single i 1) < ⊤)
    (i : Fin m) (j : Fin n) {a : Fin m → ℝ} (ha : a ∈ K j) : a i ≤ Abar K i j := by
  have h := EReal.toReal_le_toReal (coordinate_le (K j) i ha)
    (EReal.coe_ne_bot _) (ne_of_lt (hfin i j))
  simpa [Abar] using h
private theorem matrix_iff {m n : ℕ} (K : Fin n → Set (Fin m → ℝ))
    (b : Fin m → ℝ) (x : Fin n → ℝ) :
    FeasibleIb K b x ↔ (∀ A ∈ MSet K, A *ᵥ x ≤ b) ∧ 0 ≤ x := by
  classical
  change FeasibleI K (Kb b) x ↔ _
  rw [choice_iff]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨?_, hx⟩
    intro A hA i
    have hi := h (fun j i => A i j) hA
    simpa [Kb, Finset.sum_apply, Pi.smul_apply, mulVec, dotProduct, mul_comm] using hi i
  · rintro ⟨h, hx⟩
    refine ⟨hx, fun a ha => ?_⟩
    have hi := h (fun i j => a j i) ha
    intro i
    simpa [Finset.sum_apply, Pi.smul_apply, mulVec, dotProduct, mul_comm] using hi i
private theorem support_approx {m n : ℕ} (K : Fin n → Set (Fin m → ℝ))
    (hne : ∀ j, (K j).Nonempty)
    (hfin : ∀ i j, supportFun (K j) (Pi.single i 1) < ⊤)
    (i : Fin m) (j : Fin n) (ε : ℝ) (hε : 0 < ε) :
    ∃ a ∈ K j, Abar K i j - ε < a i := by
  have hreal := EReal.coe_toReal (ne_of_lt (hfin i j)) (support_not_bot (K j) (hne j) i)
  have hlt : ((Abar K i j - ε : ℝ) : EReal) < supportFun (K j) (Pi.single i 1) := by
    rw [← hreal]
    exact_mod_cast (sub_lt_self (Abar K i j) hε)
  rw [coordinate_support] at hlt
  obtain ⟨a, ha⟩ := lt_iSup_iff.mp hlt
  obtain ⟨ha, hval⟩ := lt_iSup_iff.mp ha
  exact ⟨a, ha, by exact_mod_cast hval⟩

private theorem to_lp {m n : ℕ} (K : Fin n → Set (Fin m → ℝ))
    (hne : ∀ j, (K j).Nonempty)
    (hfin : ∀ i j, supportFun (K j) (Pi.single i 1) < ⊤)
    (b : Fin m → ℝ) (x : Fin n → ℝ) (hx : FeasibleIb K b x) :
    FeasibleLP (Abar K) b x := by
  classical
  obtain ⟨hx0, hchoice⟩ := (choice_iff K (Kb b) x).mp hx
  refine ⟨hx0, fun i => ?_⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / ((n : ℝ) + 1)
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hn
  have hap : ∀ j, ∃ a ∈ K j, x j * Abar K i j ≤ x j * a i + δ := by
    intro j
    by_cases hj : x j = 0
    · obtain ⟨a, ha⟩ := hne j
      exact ⟨a, ha, by simpa [hj] using hδ.le⟩
    · have hxj : 0 < x j := lt_of_le_of_ne (hx0 j) (Ne.symm hj)
      obtain ⟨a, ha, hb⟩ := support_approx K hne hfin i j (δ / x j) (div_pos hδ hxj)
      have hc := mul_lt_mul_of_pos_left hb hxj
      have he : x j * (δ / x j) = δ := by field_simp
      refine ⟨a, ha, ?_⟩
      nlinarith
  choose a ha hab using hap
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun j _ => hab j)
  have hv : ∑ j, x j * a j i ≤ b i := by
    simpa [Kb, Finset.sum_apply, Pi.smul_apply] using hchoice a ha i
  have hδsum : (n : ℝ) * δ ≤ ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hn).2
    nlinarith
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hs
  change ∑ j, Abar K i j * x j ≤ b i + ε
  simpa [mul_comm] using hs.trans (add_le_add hv hδsum)


private theorem from_lp {m n : ℕ} (K : Fin n → Set (Fin m → ℝ))
    (hfin : ∀ i j, supportFun (K j) (Pi.single i 1) < ⊤) (b : Fin m → ℝ)
    (x : Fin n → ℝ) (hx : FeasibleLP (Abar K) b x) : FeasibleIb K b x := by
  apply (matrix_iff K b x).mpr
  refine ⟨?_, hx.1⟩
  intro A hA i
  calc
    (A *ᵥ x) i ≤ (Abar K *ᵥ x) i := by
      change ∑ j, A i j * x j ≤ ∑ j, Abar K i j * x j
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (entry_le K hfin i j (hA j)) (hx.1 j)
    _ ≤ b i := hx.2 i

private theorem ball_entry_le {m n : ℕ} (A₀ : Matrix (Fin m) (Fin n) ℝ)
    (ρ : Fin n → ℝ) (i : Fin m) (j : Fin n) {a : Fin m → ℝ}
    (ha : a ∈ hyperBall A₀ ρ j) : a i ≤ A₀ i j + ρ j := by
  have h := PiLp.norm_apply_le
    (WithLp.toLp 2 (a - fun k => A₀ k j) : EuclideanSpace ℝ (Fin m)) i
  have hn : |a i - A₀ i j| ≤
      ‖(WithLp.toLp 2 (a - fun k => A₀ k j) : EuclideanSpace ℝ (Fin m))‖ := by
    simpa using h
  have hc : |a i - A₀ i j| ≤ ρ j := hn.trans ha
  have hl := le_abs_self (a i - A₀ i j)
  linarith

private theorem ball_witness {m n : ℕ} (A₀ : Matrix (Fin m) (Fin n) ℝ)
    (ρ : Fin n → ℝ) (hρ : ∀ j, 0 ≤ ρ j) (i : Fin m) (j : Fin n) :
    ∃ a ∈ hyperBall A₀ ρ j, a i = A₀ i j + ρ j := by
  let a : Fin m → ℝ := fun k => A₀ k j + (Pi.single i (ρ j) : Fin m → ℝ) k
  have he : a - (fun k => A₀ k j) = Pi.single i (ρ j) := by
    funext k
    simp [a]
  refine ⟨a, ?_, ?_⟩
  · change ‖(WithLp.toLp 2 (a - fun k => A₀ k j) : EuclideanSpace ℝ (Fin m))‖ ≤ ρ j
    rw [he, PiLp.norm_toLp_single]
    simp [Real.norm_eq_abs, abs_of_nonneg (hρ j)]
  · simp [a]

private theorem ball_support {m n : ℕ} (A₀ : Matrix (Fin m) (Fin n) ℝ)
    (ρ : Fin n → ℝ) (hρ : ∀ j, 0 ≤ ρ j) (i : Fin m) (j : Fin n) :
    supportFun (hyperBall A₀ ρ j) (Pi.single i 1) = ((A₀ i j + ρ j : ℝ) : EReal) := by
  apply le_antisymm
  · rw [coordinate_support]
    refine iSup_le fun a => iSup_le fun ha => ?_
    exact_mod_cast ball_entry_le A₀ ρ i j ha
  · obtain ⟨a, ha, he⟩ := ball_witness A₀ ρ hρ i j
    simpa [he] using coordinate_le (hyperBall A₀ ρ j) i ha

private theorem ball_abar {m n : ℕ} (A₀ : Matrix (Fin m) (Fin n) ℝ)
    (ρ : Fin n → ℝ) (hρ : ∀ j, 0 ≤ ρ j) :
    Abar (hyperBall A₀ ρ) = A₀ + Matrix.of (fun _ j => ρ j) := by
  ext i j
  change (supportFun (hyperBall A₀ ρ j) (Pi.single i 1)).toReal = A₀ i j + ρ j
  rw [ball_support A₀ ρ hρ]
  rfl

private theorem ball_nonempty {m n : ℕ} (A₀ : Matrix (Fin m) (Fin n) ℝ)
    (ρ : Fin n → ℝ) (hρ : ∀ j, 0 ≤ ρ j) (j : Fin n) :
    (hyperBall A₀ ρ j).Nonempty := by
  refine ⟨fun i => A₀ i j, ?_⟩
  simpa [hyperBall] using hρ j

private theorem ball_feasible_iff {m n : ℕ} (A₀ : Matrix (Fin m) (Fin n) ℝ)
    (ρ : Fin n → ℝ) (hρ : ∀ j, 0 ≤ ρ j) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    FeasibleIb (hyperBall A₀ ρ) b x ↔
      (∀ j, 0 ≤ x j) ∧ ∑ j, x j • (fun i => A₀ i j + ρ j) ≤ b := by
  have hfin : ∀ i j, supportFun (hyperBall A₀ ρ j) (Pi.single i 1) < ⊤ := by
    intro i j
    rw [ball_support A₀ ρ hρ]
    exact EReal.coe_lt_top _
  have he : FeasibleIb (hyperBall A₀ ρ) b x ↔ FeasibleLP (Abar (hyperBall A₀ ρ)) b x :=
    ⟨to_lp _ (ball_nonempty A₀ ρ hρ) hfin b x, from_lp _ hfin b x⟩
  rw [he, ball_abar A₀ ρ hρ]
  simp [FeasibleLP, Pi.le_def, mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, mul_comm]

 theorem solution {m n : ℕ} (K : Fin n → Set (Fin m → ℝ))
    (hne : ∀ j, (K j).Nonempty) (hconv : ∀ j, Convex ℝ (K j))
    (hfin : ∀ i j, supportFun (K j) (Pi.single i 1) < ⊤) (b : Fin m → ℝ) :
    {x | FeasibleIb K b x} = {x | FeasibleLP (Abar K) b x} ∧
      ∀ c x : Fin n → ℝ,
        IsOptimal (FeasibleIb K b) c x ↔ IsOptimal (FeasibleLP (Abar K) b) c x := by
  have he : ∀ x, FeasibleIb K b x ↔ FeasibleLP (Abar K) b x :=
    fun x => ⟨to_lp K hne hfin b x, from_lp K hfin b x⟩
  constructor
  · ext x
    exact he x
  · intro c x
    simp only [IsOptimal, he]
