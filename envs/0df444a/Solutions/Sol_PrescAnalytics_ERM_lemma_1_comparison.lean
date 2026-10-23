-- Prove2me | solution 1 for PrescAnalytics.ERM.lemma_1_comparison
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:25:22.250122+00:00
-- url     : https://prove2.me/submissions/625d162c-6135-4374-a1a0-70a74be7e35a

import Mathlib
import Definitions.Def_PrescAnalytics_ERM_Basic



namespace PrescAnalytics.ERM

open MeasureTheory Filter Topology
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section Pair

theorem sgn_abs (b : Bool) : |signOf b| = 1 := by
  unfold signOf; split_ifs <;> simp

theorem sgn_not (b : Bool) : signOf (!b) = - signOf b := by
  cases b <;> simp [signOf]

def flipk {d : ℕ} (k : Fin d) (ρ : Fin d → Bool) : Fin d → Bool := Function.update ρ k (!ρ k)

theorem flipk_invol {d : ℕ} (k : Fin d) : Function.Involutive (flipk k) := by
  intro ρ; funext j; unfold flipk
  by_cases h : j = k
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem flipk_self {d : ℕ} (k : Fin d) (ρ : Fin d → Bool) : flipk k ρ k = !ρ k := by
  simp [flipk]

theorem flipk_ne {d : ℕ} {k j : Fin d} (h : j ≠ k) (ρ : Fin d → Bool) : flipk k ρ j = ρ j := by
  simp [flipk, Function.update_of_ne h]

theorem sg_sum_zero {d : ℕ} (k : Fin d) : ∑ ρ : Fin d → Bool, signOf (ρ k) = 0 := by
  have h := Equiv.sum_comp (flipk_invol k).toPerm (fun ρ : Fin d → Bool => signOf (ρ k))
  simp only [Function.Involutive.coe_toPerm, flipk_self, sgn_not, Finset.sum_neg_distrib] at h
  linarith

theorem card_signs (d : ℕ) : (Fintype.card (Fin d → Bool) : ℝ) = 2 ^ d := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; push_cast; ring

theorem pair_lemma {ι : Type*} [Nonempty ι] {d : ℕ} (hd : 0 < d) (L : ℝ) (hL : 0 ≤ L)
    (a C : ι → ℝ) (w : ι → Fin d → ℝ) (B : ℝ)
    (ha : ∀ f, |a f| ≤ B) (hC : ∀ f, |C f| ≤ B) (hw : ∀ f k, |w f k| ≤ B)
    (hLip : ∀ f f', C f - C f' ≤ L * ‖w f - w f'‖) :
    (2:ℝ) ^ (d - 1) * ((⨆ f, (a f + C f)) + (⨆ f, (a f - C f)))
      ≤ ∑ ρ : Fin d → Bool, ⨆ f, (a f + L * ∑ k, signOf (ρ k) * w f k) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hB : 0 ≤ B := (abs_nonneg _).trans (ha (Classical.arbitrary ι))
  have hbp : BddAbove (Set.range fun f => a f + C f) :=
    ⟨2 * B, by rintro _ ⟨f, rfl⟩; have := (abs_le.mp (ha f)).2; have := (abs_le.mp (hC f)).2; simp only; linarith⟩
  have hbm : BddAbove (Set.range fun f => a f - C f) :=
    ⟨2 * B, by rintro _ ⟨f, rfl⟩; have := (abs_le.mp (ha f)).2; have := (abs_le.mp (hC f)).1; simp only; linarith⟩
  have hsw : ∀ (ρ : Fin d → Bool) f, |∑ k, signOf (ρ k) * w f k| ≤ d * B := by
    intro ρ f
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |signOf (ρ k) * w f k| ≤ ∑ _k : Fin d, B := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul, sgn_abs, one_mul]; exact hw f k
      _ = d * B := by simp
  have hbq : ∀ ρ : Fin d → Bool, BddAbove (Set.range fun f => a f + L * ∑ k, signOf (ρ k) * w f k) := by
    intro ρ
    refine ⟨B + L * (d * B), ?_⟩
    rintro _ ⟨f, rfl⟩
    have h1 := (abs_le.mp (ha f)).2
    have h2 := (abs_le.mp (hsw ρ f)).2
    have := mul_le_mul_of_nonneg_left h2 hL
    simp only; linarith
  set Q : (Fin d → Bool) → ℝ := fun ρ => ⨆ f, (a f + L * ∑ k, signOf (ρ k) * w f k) with hQ
  have hQge : ∀ ρ f, a f + L * ∑ k, signOf (ρ k) * w f k ≤ Q ρ :=
    fun ρ f => le_ciSup (hbq ρ) f
  have h2d : (2:ℝ) ^ d = 2 * 2 ^ (d - 1) := by
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp [pow_succ]; ring
  have hmain : ∀ ε : ℝ, 0 < ε → (2:ℝ) ^ (d - 1) * ((⨆ f, (a f + C f)) + (⨆ f, (a f - C f)))
      ≤ ∑ ρ, Q ρ + ε := by
    intro ε hε
    set δ := ε / 2 ^ d with hδ
    have hpow : (0:ℝ) < 2 ^ d := by positivity
    have hδ0 : 0 < δ := by positivity
    obtain ⟨f, hf⟩ := exists_lt_of_lt_ciSup (f := fun f => a f + C f)
      (show (⨆ f, (a f + C f)) - δ < ⨆ f, (a f + C f) by linarith)
    obtain ⟨f', hf'⟩ := exists_lt_of_lt_ciSup (f := fun f => a f - C f)
      (show (⨆ f, (a f - C f)) - δ < ⨆ f, (a f - C f) by linarith)
    obtain ⟨ks, hks⟩ := Finite.exists_max (fun k : Fin d => |w f k - w f' k|)
    have hnorm : ‖w f - w f'‖ ≤ |w f ks - w f' ks| := by
      refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun k => ?_
      simpa [Real.norm_eq_abs] using hks k
    have hCl : C f - C f' ≤ L * |w f ks - w f' ks| :=
      (hLip f f').trans (mul_le_mul_of_nonneg_left hnorm hL)
    set Δ := w f ks - w f' ks with hΔ
    set X := (a f + C f) + (a f' - C f') with hX
    set u : Fin d → ℝ := fun k => w f k + w f' k with hu
    have key : ∀ ρ : Fin d → Bool, X + L * ∑ k ∈ Finset.univ.erase ks, signOf (ρ k) * u k
        ≤ Q ρ + Q (flipk ks ρ) := by
      intro ρ
      have hsplit : ∀ (σ : Fin d → Bool) (g : Fin d → ℝ),
          ∑ k, signOf (σ k) * g k = signOf (σ ks) * g ks
            + ∑ k ∈ Finset.univ.erase ks, signOf (σ k) * g k := by
        intro σ g
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ks)]
      have hflip : ∀ g : Fin d → ℝ, ∑ k ∈ Finset.univ.erase ks, signOf (flipk ks ρ k) * g k
          = ∑ k ∈ Finset.univ.erase ks, signOf (ρ k) * g k := by
        intro g
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [flipk_ne (Finset.ne_of_mem_erase hk)]
      have hsa : |signOf (ρ ks)| = 1 := sgn_abs _
      by_cases hs : 0 ≤ signOf (ρ ks) * Δ
      · have h1 := hQge ρ f
        have h2 := hQge (flipk ks ρ) f'
        rw [hsplit ρ (w f)] at h1
        rw [hsplit (flipk ks ρ) (w f'), flipk_self, sgn_not, hflip] at h2
        have habs : signOf (ρ ks) * Δ = |Δ| := by
          rw [← abs_of_nonneg hs, abs_mul, hsa, one_mul]
        have e1 : ∑ k ∈ Finset.univ.erase ks, signOf (ρ k) * u k
            = ∑ k ∈ Finset.univ.erase ks, signOf (ρ k) * w f k
              + ∑ k ∈ Finset.univ.erase ks, signOf (ρ k) * w f' k := by
          rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun k _ => ?_
          simp only [hu]; ring
        have e2 : signOf (ρ ks) * w f ks - signOf (ρ ks) * w f' ks = |Δ| := by
          rw [← habs, hΔ]; ring
        have : L * (signOf (ρ ks) * Δ) = L * |Δ| := by rw [habs]
        nlinarith [hCl, e1, e2, mul_comm L (signOf (ρ ks) * Δ)]
      · push_neg at hs
        have h1 := hQge ρ f'
        have h2 := hQge (flipk ks ρ) f
        rw [hsplit ρ (w f')] at h1
        rw [hsplit (flipk ks ρ) (w f), flipk_self, sgn_not, hflip] at h2
        have habs : -(signOf (ρ ks) * Δ) = |Δ| := by
          rw [← abs_of_neg hs, abs_mul, hsa, one_mul]
        have e1 : ∑ k ∈ Finset.univ.erase ks, signOf (ρ k) * u k
            = ∑ k ∈ Finset.univ.erase ks, signOf (ρ k) * w f' k
              + ∑ k ∈ Finset.univ.erase ks, signOf (ρ k) * w f k := by
          rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun k _ => ?_
          simp only [hu]; ring
        have e2 : signOf (ρ ks) * w f' ks - signOf (ρ ks) * w f ks = |Δ| := by
          rw [← habs, hΔ]; ring
        nlinarith [hCl, e1, e2]
    -- sum
    have hsumQ : ∑ ρ, (Q ρ + Q (flipk ks ρ)) = 2 * ∑ ρ, Q ρ := by
      have h := Equiv.sum_comp (flipk_invol ks).toPerm Q
      simp only [Function.Involutive.coe_toPerm] at h
      rw [Finset.sum_add_distrib, h]; ring
    have hzero : ∑ ρ : Fin d → Bool, (∑ k ∈ Finset.univ.erase ks, signOf (ρ k) * u k) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun k _ => ?_
      simp_rw [← Finset.sum_mul]
      rw [sg_sum_zero]; ring
    have hlow : ∑ ρ : Fin d → Bool, (X + L * ∑ k ∈ Finset.univ.erase ks, signOf (ρ k) * u k)
        ≤ ∑ ρ, (Q ρ + Q (flipk ks ρ)) := Finset.sum_le_sum fun ρ _ => key ρ
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hzero, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, card_signs, hsumQ] at hlow
    have hXl : (⨆ f, (a f + C f)) + (⨆ f, (a f - C f)) - 2 * δ < X := by
      rw [hX]; linarith
    have : (2:ℝ) ^ d * ((⨆ f, (a f + C f)) + (⨆ f, (a f - C f)) - 2 * δ) ≤ 2 * ∑ ρ, Q ρ := by
      calc (2:ℝ) ^ d * ((⨆ f, (a f + C f)) + (⨆ f, (a f - C f)) - 2 * δ) ≤ 2 ^ d * X :=
            mul_le_mul_of_nonneg_left hXl.le hpow.le
        _ ≤ _ := by linarith
    have hεδ : (2:ℝ) ^ d * δ = ε := by rw [hδ]; field_simp
    rw [h2d] at this hεδ
    nlinarith
  exact le_of_forall_pos_le_add fun ε hε => hmain ε hε

end Pair

section Core

theorem sum_cons_fin {β : Type*} [Fintype β] (N : ℕ) (F : (Fin (N+1) → β) → ℝ) :
    ∑ σ, F σ = ∑ b : β, ∑ σ' : Fin N → β, F (Fin.cons b σ') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => β)) _ _ (fun p => rfl)).symm

theorem core_ind {ι : Type*} [Nonempty ι] {d : ℕ} (hd : 0 < d) (L : ℝ) (hL : 0 ≤ L)
    (M K : ℝ) :
    ∀ (N : ℕ) (v : ι → Fin N → Fin d → ℝ) (C : Fin N → (Fin d → ℝ) → ℝ)
      (_hv : ∀ f i k, |v f i k| ≤ M) (_hCb : ∀ f i, |C i (v f i)| ≤ K)
      (_hLip : ∀ i z z', C i z - C i z' ≤ L * ‖z - z'‖)
      (a : ι → ℝ) (K0 : ℝ) (_ha : ∀ f, |a f| ≤ K0),
      (2:ℝ) ^ (N * (d - 1)) * ∑ τ : Fin N → Bool, ⨆ f, (a f + ∑ i, signOf (τ i) * C i (v f i))
        ≤ ∑ σ : Fin N → Fin d → Bool, ⨆ f, (a f + L * ∑ i, ∑ k, signOf (σ i k) * v f i k) := by
  intro N
  induction N with
  | zero =>
    intro v C hv hCb hLip a K0 ha
    simp
  | succ N ih =>
    intro v C hv hCb hLip a K0 ha
    obtain ⟨f0⟩ := (inferInstance : Nonempty ι)
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hv f0 0 ⟨0, hd⟩)
    have hK0 : 0 ≤ K := (abs_nonneg _).trans (hCb f0 0)
    have hK00 : 0 ≤ K0 := (abs_nonneg _).trans (ha f0)
    -- left side decomposition
    have hLHS : ∑ τ : Fin (N+1) → Bool, ⨆ f, (a f + ∑ i, signOf (τ i) * C i (v f i))
        = ∑ b : Bool, ∑ τ' : Fin N → Bool, ⨆ f,
            ((a f + signOf b * C 0 (v f 0)) + ∑ i : Fin N, signOf (τ' i) *
              (fun (i : Fin N) z => C i.succ z) i ((fun f (i : Fin N) => v f i.succ) f i)) := by
      rw [sum_cons_fin]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun τ' _ => ?_
      congr 1; funext f
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      ring
    -- apply IH for each b
    have hIH : ∀ b : Bool, (2:ℝ) ^ (N * (d - 1)) * ∑ τ' : Fin N → Bool, ⨆ f,
            ((a f + signOf b * C 0 (v f 0)) + ∑ i : Fin N, signOf (τ' i) *
              (fun (i : Fin N) z => C i.succ z) i ((fun f (i : Fin N) => v f i.succ) f i))
        ≤ ∑ σ' : Fin N → Fin d → Bool, ⨆ f, ((a f + signOf b * C 0 (v f 0)) + L *
            ∑ i : Fin N, ∑ k, signOf (σ' i k) * (fun f (i : Fin N) => v f i.succ) f i k) := by
      intro b
      refine ih (fun f (i : Fin N) => v f i.succ) (fun (i : Fin N) z => C i.succ z)
        (fun f i k => hv f i.succ k) (fun f i => hCb f i.succ) (fun i z z' => hLip i.succ z z')
        (fun f => a f + signOf b * C 0 (v f 0)) (K0 + K) (fun f => ?_)
      calc |a f + signOf b * C 0 (v f 0)| ≤ |a f| + |signOf b * C 0 (v f 0)| := abs_add_le _ _
        _ ≤ K0 + K := by
          rw [abs_mul, sgn_abs, one_mul]; exact add_le_add (ha f) (hCb f 0)
    -- right side decomposition
    have hRHS : ∑ σ : Fin (N+1) → Fin d → Bool, ⨆ f,
          (a f + L * ∑ i, ∑ k, signOf (σ i k) * v f i k)
        = ∑ σ' : Fin N → Fin d → Bool, ∑ ρ : Fin d → Bool, ⨆ f,
          ((a f + L * ∑ i : Fin N, ∑ k, signOf (σ' i k) * v f i.succ k)
            + L * ∑ k, signOf (ρ k) * (fun f => v f 0) f k) := by
      rw [sum_cons_fin, Finset.sum_comm]
      refine Finset.sum_congr rfl fun σ' _ => Finset.sum_congr rfl fun ρ _ => ?_
      congr 1; funext f
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      ring
    -- per σ' inequality via pair lemma
    set B : ℝ := K0 + K + M + L * (N * (d * M)) with hB
    have hLNM : 0 ≤ L * (N * (d * M)) := by positivity
    have hpair : ∀ σ' : Fin N → Fin d → Bool,
        (2:ℝ) ^ (d - 1) * ∑ b : Bool, ⨆ f, (((a f + L * ∑ i : Fin N, ∑ k, signOf (σ' i k) * v f i.succ k))
            + signOf b * C 0 (v f 0))
        ≤ ∑ ρ : Fin d → Bool, ⨆ f,
          ((a f + L * ∑ i : Fin N, ∑ k, signOf (σ' i k) * v f i.succ k)
            + L * ∑ k, signOf (ρ k) * (fun f => v f 0) f k) := by
      intro σ'
      have hR : ∀ f, |L * ∑ i : Fin N, ∑ k, signOf (σ' i k) * v f i.succ k| ≤ L * (N * (d * M)) := by
        intro f
        rw [abs_mul, abs_of_nonneg hL]
        refine mul_le_mul_of_nonneg_left ?_ hL
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i : Fin N, |∑ k, signOf (σ' i k) * v f i.succ k| ≤ ∑ _i : Fin N, (d * M) := by
              refine Finset.sum_le_sum fun i _ => ?_
              refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
              calc ∑ k, |signOf (σ' i k) * v f i.succ k| ≤ ∑ _k : Fin d, M := by
                    refine Finset.sum_le_sum fun k _ => ?_
                    rw [abs_mul, sgn_abs, one_mul]; exact hv f i.succ k
                _ = d * M := by simp
          _ = N * (d * M) := by simp
      have hp := pair_lemma hd L hL (fun f => a f + L * ∑ i : Fin N, ∑ k, signOf (σ' i k) * v f i.succ k)
        (fun f => C 0 (v f 0)) (fun f => v f 0) B
        (fun f => (abs_add_le _ _).trans (by have := ha f; have := hR f; rw [hB]; linarith))
        (fun f => (hCb f 0).trans (by rw [hB]; linarith))
        (fun f k => (hv f 0 k).trans (by rw [hB]; linarith))
        (fun f f' => hLip 0 (v f 0) (v f' 0))
      have e : ∑ b : Bool, ⨆ f, (((a f + L * ∑ i : Fin N, ∑ k, signOf (σ' i k) * v f i.succ k))
            + signOf b * C 0 (v f 0))
          = (⨆ f, ((a f + L * ∑ i : Fin N, ∑ k, signOf (σ' i k) * v f i.succ k) + C 0 (v f 0)))
            + ⨆ f, ((a f + L * ∑ i : Fin N, ∑ k, signOf (σ' i k) * v f i.succ k) - C 0 (v f 0)) := by
        rw [Fintype.sum_bool]
        simp only [signOf, if_true, Bool.false_eq_true, if_false]
        congr 2
        · funext f; ring
        · funext f; ring
      rw [e]; exact hp
    have hT : ∀ (b : Bool) (σ' : Fin N → Fin d → Bool), ⨆ f, ((a f + signOf b * C 0 (v f 0)) + L *
            ∑ i : Fin N, ∑ k, signOf (σ' i k) * (fun f (i : Fin N) => v f i.succ) f i k)
        = ⨆ f, (((a f + L * ∑ i : Fin N, ∑ k, signOf (σ' i k) * v f i.succ k))
            + signOf b * C 0 (v f 0)) := by
      intro b σ'; congr 1; funext f; ring
    rw [hLHS, hRHS]
    have hpow : (2:ℝ) ^ ((N + 1) * (d - 1)) = 2 ^ (d - 1) * 2 ^ (N * (d - 1)) := by
      rw [← pow_add]; congr 1; ring
    calc (2:ℝ) ^ ((N + 1) * (d - 1)) * ∑ b : Bool, ∑ τ' : Fin N → Bool, ⨆ f,
            ((a f + signOf b * C 0 (v f 0)) + ∑ i : Fin N, signOf (τ' i) *
              (fun (i : Fin N) z => C i.succ z) i ((fun f (i : Fin N) => v f i.succ) f i))
        = (2:ℝ) ^ (d - 1) * ∑ b : Bool, ((2:ℝ) ^ (N * (d - 1)) * ∑ τ' : Fin N → Bool, ⨆ f,
            ((a f + signOf b * C 0 (v f 0)) + ∑ i : Fin N, signOf (τ' i) *
              (fun (i : Fin N) z => C i.succ z) i ((fun f (i : Fin N) => v f i.succ) f i))) := by
          rw [hpow, mul_assoc, Finset.mul_sum]
      _ ≤ (2:ℝ) ^ (d - 1) * ∑ b : Bool, ∑ σ' : Fin N → Fin d → Bool, ⨆ f,
            (((a f + L * ∑ i : Fin N, ∑ k, signOf (σ' i k) * v f i.succ k))
              + signOf b * C 0 (v f 0)) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => ?_) (by positivity)
          refine (hIH b).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun σ' _ => hT b σ'
      _ = ∑ σ' : Fin N → Fin d → Bool, (2:ℝ) ^ (d - 1) * ∑ b : Bool, ⨆ f,
            (((a f + L * ∑ i : Fin N, ∑ k, signOf (σ' i k) * v f i.succ k))
              + signOf b * C 0 (v f 0)) := by
          rw [Finset.sum_comm, Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun σ' _ => hpair σ'

end Core

section L3
variable {X Y : Type*} {d N : ℕ}

theorem S_not (F : Set (X → Fin d → ℝ)) (x : Fin N → X) (σ : Fin N → Fin d → Bool)
    (f : X → Fin d → ℝ) :
    ∑ i, ∑ k, signOf ((fun i k => !(σ i k)) i k) * f (x i) k
      = - ∑ i, ∑ k, signOf (σ i k) * f (x i) k := by
  simp only [sgn_not, neg_mul, Finset.sum_neg_distrib]

theorem S_diff (x : Fin N → X) (i : Fin N) (k : Fin d) (f : X → Fin d → ℝ) :
    ∑ i', ∑ k', signOf ((fun (_ : Fin N) (_ : Fin d) => true) i' k') * f (x i') k'
      - ∑ i', ∑ k', signOf ((Function.update (fun (_ : Fin N) (_ : Fin d) => true) i
          (Function.update (fun (_ : Fin d) => true) k false)) i' k') * f (x i') k'
      = 2 * f (x i) k := by
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · rw [← Finset.sum_sub_distrib, Finset.sum_eq_single k]
    · simp [signOf]; ring
    · intro k' _ hk'
      simp [Function.update_of_ne hk']
    · simp
  · intro i' _ hi'
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun k' _ => ?_
    simp [Function.update_of_ne hi']
  · simp

theorem coord_bound (F : Set (X → Fin d → ℝ)) (x : Fin N → X)
    (hfin : ∀ σ : Fin N → Fin d → Bool,
      BddAbove (Set.range fun f : F => ∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (f : F) i k, |f.1 (x i) k| ≤ M := by
  choose B hB using hfin
  set M0 : ℝ := ∑ σ : Fin N → Fin d → Bool, |B σ| with hM0
  have hM0nn : 0 ≤ M0 := Finset.sum_nonneg fun σ _ => abs_nonneg _
  have hle : ∀ σ, |B σ| ≤ M0 := fun σ =>
    Finset.single_le_sum (f := fun σ => |B σ|) (fun σ _ => abs_nonneg _) (Finset.mem_univ σ)
  have hS : ∀ (σ : Fin N → Fin d → Bool) (f : F),
      |∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k| ≤ M0 := by
    intro σ f
    rw [abs_le]
    constructor
    · have h1 : ∑ i, ∑ k, signOf ((fun i k => !(σ i k)) i k) * f.1 (x i) k ≤ B (fun i k => !(σ i k)) :=
        hB _ ⟨f, rfl⟩
      rw [S_not F x σ f.1] at h1
      have := hle (fun i k => !(σ i k)); have := le_abs_self (B fun i k => !(σ i k))
      linarith
    · have h1 : ∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k ≤ B σ := hB σ ⟨f, rfl⟩
      have := hle σ; have := le_abs_self (B σ)
      linarith
  refine ⟨M0, hM0nn, fun f i k => ?_⟩
  have hd := S_diff x i k f.1
  have h1 := hS (fun _ _ => true) f
  have h2 := hS (Function.update (fun (_ : Fin N) (_ : Fin d) => true) i
          (Function.update (fun (_ : Fin d) => true) k false)) f
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end L3

section L4
variable {X Y : Type*} {d N : ℕ}

theorem real_step (hd : 0 < d) (F : Set (X → Fin d → ℝ)) [Nonempty F]
    (c : (Fin d → ℝ) → Y → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hc_lip : ∀ (z z' : Fin d → ℝ) (y : Y), |c z y - c z' y| ≤ L * ‖z - z'‖)
    (x : Fin N → X) (y : Fin N → Y)
    (hfin : ∀ σ : Fin N → Fin d → Bool,
      BddAbove (Set.range fun f : F => ∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k)) :
    (∀ τ : Fin N → Bool,
        BddAbove (Set.range fun f : F => ∑ i, signOf (τ i) * c (f.1 (x i)) (y i))) ∧
    (2:ℝ) ^ (N * (d - 1)) * ∑ τ : Fin N → Bool, ⨆ f : F, ∑ i, signOf (τ i) * c (f.1 (x i)) (y i)
      ≤ L * ∑ σ : Fin N → Fin d → Bool, ⨆ f : F, ∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k := by
  obtain ⟨M, hM0, hM⟩ := coord_bound F x hfin
  set K : ℝ := ∑ i, |c 0 (y i)| + L * M with hK
  have hnorm : ∀ (f : F) i, ‖f.1 (x i)‖ ≤ M := fun f i =>
    (pi_norm_le_iff_of_nonneg hM0).2 fun k => by simpa [Real.norm_eq_abs] using hM f i k
  have hC : ∀ (f : F) i, |c (f.1 (x i)) (y i)| ≤ K := by
    intro f i
    have h1 := hc_lip (f.1 (x i)) 0 (y i)
    rw [sub_zero] at h1
    have h2 : |c (f.1 (x i)) (y i)| ≤ |c 0 (y i)| + L * M := by
      calc |c (f.1 (x i)) (y i)| = |(c (f.1 (x i)) (y i) - c 0 (y i)) + c 0 (y i)| := by ring_nf
        _ ≤ |c (f.1 (x i)) (y i) - c 0 (y i)| + |c 0 (y i)| := abs_add_le _ _
        _ ≤ L * ‖f.1 (x i)‖ + |c 0 (y i)| := add_le_add h1 le_rfl
        _ ≤ L * M + |c 0 (y i)| := by gcongr; exact hnorm f i
        _ = _ := by ring
    have h3 : |c 0 (y i)| ≤ ∑ j, |c 0 (y j)| :=
      Finset.single_le_sum (f := fun j => |c 0 (y j)|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    rw [hK]; linarith
  have hT : ∀ τ : Fin N → Bool,
      BddAbove (Set.range fun f : F => ∑ i, signOf (τ i) * c (f.1 (x i)) (y i)) := by
    intro τ
    refine ⟨N * K, ?_⟩
    rintro _ ⟨f, rfl⟩
    have : |∑ i, signOf (τ i) * c (f.1 (x i)) (y i)| ≤ N * K := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |signOf (τ i) * c (f.1 (x i)) (y i)| ≤ ∑ _i : Fin N, K :=
            Finset.sum_le_sum fun i _ => by rw [abs_mul, sgn_abs, one_mul]; exact hC f i
        _ = N * K := by simp
    exact (abs_le.mp this).2
  refine ⟨hT, ?_⟩
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hcore := core_ind hd L hL M K N (fun (f : F) i => f.1 (x i)) (fun i z => c z (y i))
    (fun f i k => hM f i k) (fun f i => hC f i)
    (fun i z z' => (le_abs_self _).trans (hc_lip z z' (y i))) (fun _ => 0) 0 (fun _ => by simp)
  simp only [zero_add] at hcore
  have hmul : ∀ σ : Fin N → Fin d → Bool, (⨆ f : F, L * ∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k)
      = L * ⨆ f : F, ∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k := fun σ =>
    (Real.mul_iSup_of_nonneg hL _).symm
  simp only [hmul, ← Finset.mul_sum] at hcore
  exact hcore

theorem iSup_coe_bdd {ι : Type*} [Nonempty ι] (g : ι → ℝ) (h : (⨆ i, (g i : EReal)) ≠ ⊤) :
    BddAbove (Set.range g) := by
  have hbot : (⨆ i, (g i : EReal)) ≠ ⊥ := by
    intro hb
    have i0 := Classical.arbitrary ι
    have := le_iSup (fun i => (g i : EReal)) i0
    rw [hb] at this
    exact EReal.coe_ne_bot _ (le_bot_iff.mp this)
  refine ⟨(⨆ i, (g i : EReal)).toReal, ?_⟩
  rintro _ ⟨i, rfl⟩
  have := le_iSup (fun i => (g i : EReal)) i
  rw [← EReal.coe_le_coe_iff, EReal.coe_toReal h hbot]; exact this

theorem ereal_sum_ne_bot {ι : Type*} (s : Finset ι) (f : ι → EReal) (h : ∀ i ∈ s, f i ≠ ⊥) :
    ∑ i ∈ s, f i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact EReal.add_ne_bot_iff.mpr ⟨h j (Finset.mem_insert_self _ _),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)⟩

theorem ereal_sum_top {ι : Type*} (s : Finset ι) (f : ι → EReal) (h : ∀ i ∈ s, f i ≠ ⊥)
    (i0 : ι) (hi0 : i0 ∈ s) (hf : f i0 = ⊤) : ∑ i ∈ s, f i = ⊤ := by
  classical
  rw [← Finset.add_sum_erase s f hi0, hf]
  exact EReal.top_add_of_ne_bot (ereal_sum_ne_bot _ _ fun i hi => h i (Finset.mem_of_mem_erase hi))

theorem ereal_sum_bot {ι : Type*} (s : Finset ι) (hs : s.Nonempty) :
    ∑ _i ∈ s, (⊥ : EReal) = ⊥ := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a s ha hs ih => rw [Finset.sum_cons, ih]; simp

theorem signedSup_cost (F : Set (X → Fin d → ℝ)) (c : (Fin d → ℝ) → Y → ℝ) (s : Fin N → X × Y)
    (σ : Fin N → Fin 1 → Bool) :
    signedSup (liftClass (costClass c F)) s σ
      = ⨆ f : F, ((∑ i, signOf (σ i 0) * c (f.1 (s i).1) (s i).2 : ℝ) : EReal) := by
  have himg : liftClass (costClass c F)
      = (fun f : X → Fin d → ℝ => fun (p : X × Y) (_ : Fin 1) => c (f p.1) p.2) '' F := by
    ext g'; constructor
    · rintro ⟨g, ⟨f, hf, rfl⟩, rfl⟩; exact ⟨f, hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩; exact ⟨_, ⟨f, hf, rfl⟩, rfl⟩
  unfold signedSup
  rw [himg, iSup_image]
  have : ∀ f : X → Fin d → ℝ, (∑ i, ∑ k : Fin 1, signOf (σ i k) *
      (fun (p : X × Y) (_ : Fin 1) => c (f p.1) p.2) (s i) k)
      = ∑ i, signOf (σ i 0) * c (f (s i).1) (s i).2 := by intro f; simp
  simp only [this]
  exact (iSup_subtype'' F (fun f => ((∑ i, signOf (σ i 0) * c (f (s i).1) (s i).2 : ℝ) : EReal))).symm

theorem signedSup_eq' (F : Set (X → Fin d → ℝ)) (x : Fin N → X) (σ : Fin N → Fin d → Bool) :
    signedSup F x σ = ⨆ f : F, ((∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k : ℝ) : EReal) := by
  unfold signedSup
  exact (iSup_subtype'' F (fun f => ((∑ i, ∑ k, signOf (σ i k) * f (x i) k : ℝ) : EReal))).symm

end L4

section L5
variable {X Y : Type*} {d N : ℕ}

theorem ereal_iSup_coe' {ι : Type*} [Nonempty ι] (f : ι → ℝ) (hf : BddAbove (Set.range f)) :
    (⨆ i, (f i : EReal)) = ((⨆ i, f i : ℝ) : EReal) := by
  have := Monotone.map_ciSup_of_continuousAt (f := ((↑) : ℝ → EReal)) (g := f)
    continuous_coe_real_ereal.continuousAt (fun a b h => EReal.coe_le_coe_iff.mpr h) hf
  exact this.symm

theorem ereal_coe_sum' {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, EReal.coe_add, ih]

theorem lemma1_i (F : Set (X → Fin d → ℝ)) (c : (Fin d → ℝ) → Y → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hc_lip : ∀ (z z' : Fin d → ℝ) (y : Y), |c z y - c z' y| ≤ L * ‖z - z'‖)
    (s : Fin N → X × Y) :
    empRademacherR (costClass c F) s ≤ (L : EReal) * empRademacher F (fun i => (s i).1) := by
  classical
  unfold empRademacherR empRademacher
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc1 : (0 : ℝ) < 2 / N / 2 ^ (N * 1) := by positivity
  have hc2 : (0 : ℝ) < 2 / N / 2 ^ (N * d) := by positivity
  rcases F.eq_empty_or_nonempty with hF | ⟨f0, hf0⟩
  · subst hF
    have hsb : ∀ σ : Fin N → Fin 1 → Bool,
        signedSup (liftClass (costClass c (∅ : Set (X → Fin d → ℝ)))) s σ = ⊥ := by
      intro σ
      have : liftClass (costClass c (∅ : Set (X → Fin d → ℝ))) = ∅ := by
        ext g; simp [liftClass, costClass]
      rw [this]; simp [signedSup]
    simp only [hsb]
    rw [ereal_sum_bot _ Finset.univ_nonempty, EReal.coe_mul_bot_of_pos hc1]
    exact bot_le
  haveI : Nonempty F := ⟨⟨f0, hf0⟩⟩
  set x : Fin N → X := fun i => (s i).1 with hx
  set y : Fin N → Y := fun i => (s i).2 with hy
  simp only [signedSup_cost, signedSup_eq' F x]
  -- left side as a sum over τ
  have eL : ∑ σ : Fin N → Fin 1 → Bool,
        (⨆ f : F, ((∑ i, signOf (σ i 0) * c (f.1 (s i).1) (s i).2 : ℝ) : EReal))
      = ∑ τ : Fin N → Bool,
        (⨆ f : F, ((∑ i, signOf (τ i) * c (f.1 (x i)) (y i) : ℝ) : EReal)) :=
    Fintype.sum_equiv (Equiv.piCongrRight fun _ => Equiv.funUnique (Fin 1) Bool) _ _
      (fun σ => rfl)
  rw [eL]
  by_cases hdeg : d = 0 ∨ L = 0
  · -- degenerate case
    have hceq : ∀ (z z' : Fin d → ℝ) (y : Y), c z y = c z' y := by
      intro z z' y
      have h := hc_lip z z' y
      have : L * ‖z - z'‖ = 0 := by
        rcases hdeg with h0 | h0
        · subst h0
          have : z - z' = 0 := Subsingleton.elim _ _
          rw [this]; simp
        · rw [h0]; ring
      rw [this] at h
      have := abs_nonneg (c z y - c z' y)
      have h0 : |c z y - c z' y| = 0 := le_antisymm h this
      linarith [abs_eq_zero.mp h0]
    have hL0 : ∀ τ : Fin N → Bool,
        (⨆ f : F, ((∑ i, signOf (τ i) * c (f.1 (x i)) (y i) : ℝ) : EReal))
          = ((∑ i, signOf (τ i) * c (f0 (x i)) (y i) : ℝ) : EReal) := by
      intro τ
      have : (fun f : F => ((∑ i, signOf (τ i) * c (f.1 (x i)) (y i) : ℝ) : EReal))
          = fun _ => ((∑ i, signOf (τ i) * c (f0 (x i)) (y i) : ℝ) : EReal) := by
        funext f; congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hceq (f.1 (x i)) (f0 (x i))]
      rw [this]; exact iSup_const
    simp only [hL0]
    have hz : ∑ τ : Fin N → Bool, ((∑ i, signOf (τ i) * c (f0 (x i)) (y i) : ℝ) : EReal) = 0 := by
      rw [← ereal_coe_sum']
      have : ∑ τ : Fin N → Bool, ∑ i, signOf (τ i) * c (f0 (x i)) (y i) = 0 := by
        rw [Finset.sum_comm]
        refine Finset.sum_eq_zero fun i _ => ?_
        simp_rw [← Finset.sum_mul]
        rw [sg_sum_zero]; ring
      rw [this]; rfl
    rw [hz, mul_zero]
    -- right side is zero
    rcases hdeg with h0 | h0
    · subst h0
      have : ∀ σ : Fin N → Fin 0 → Bool,
          (⨆ f : F, ((∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k : ℝ) : EReal)) = 0 := by
        intro σ; simp
      simp only [this]; simp
    · rw [h0]; simp
  · push_neg at hdeg
    obtain ⟨hd0, hL0⟩ := hdeg
    have hd : 0 < d := Nat.pos_of_ne_zero hd0
    have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    by_cases hb : ∃ σ : Fin N → Fin d → Bool,
        (⨆ f : F, ((∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k : ℝ) : EReal)) = ⊤
    · obtain ⟨σ0, hσ0⟩ := hb
      have hnb : ∀ σ : Fin N → Fin d → Bool,
          (⨆ f : F, ((∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k : ℝ) : EReal)) ≠ ⊥ := by
        intro σ hbot
        have := le_iSup (fun f : F => ((∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k : ℝ) : EReal))
          ⟨f0, hf0⟩
        rw [hbot] at this
        exact EReal.coe_ne_bot _ (le_bot_iff.mp this)
      rw [ereal_sum_top _ _ (fun σ _ => hnb σ) σ0 (Finset.mem_univ _) hσ0,
        EReal.coe_mul_top_of_pos hc2, EReal.coe_mul_top_of_pos hLpos]
      exact le_top
    · push_neg at hb
      have hfin : ∀ σ : Fin N → Fin d → Bool,
          BddAbove (Set.range fun f : F => ∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k) :=
        fun σ => iSup_coe_bdd _ (hb σ)
      obtain ⟨hT, hineq⟩ := real_step hd F c L hL hc_lip x y hfin
      simp only [ereal_iSup_coe' _ (hfin _), ereal_iSup_coe' _ (hT _)]
      rw [← ereal_coe_sum', ← ereal_coe_sum', ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul]
      rw [EReal.coe_le_coe_iff]
      -- real inequality
      have hnd : N * d = N + N * (d - 1) := by
        obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
        rw [he, Nat.add_sub_cancel]; ring
      have hp : (2:ℝ) ^ (N * d) = 2 ^ N * 2 ^ (N * (d - 1)) := by rw [hnd, pow_add]
      have hp1 : (0:ℝ) < 2 ^ N := by positivity
      have hp2 : (0:ℝ) < 2 ^ (N * (d - 1)) := by positivity
      rw [Nat.mul_one, hp]
      set A := ∑ τ : Fin N → Bool, ⨆ f : F, ∑ i, signOf (τ i) * c (f.1 (x i)) (y i) with hA
      set Bsum := ∑ σ : Fin N → Fin d → Bool, ⨆ f : F, ∑ i, ∑ k, signOf (σ i k) * f.1 (x i) k
        with hBs
      have h1 : 2 / (N:ℝ) / 2 ^ N * A = 2 / (N:ℝ) / (2 ^ N * 2 ^ (N * (d - 1))) *
          (2 ^ (N * (d - 1)) * A) := by field_simp
      rw [h1]
      calc 2 / (N:ℝ) / (2 ^ N * 2 ^ (N * (d - 1))) * (2 ^ (N * (d - 1)) * A)
          ≤ 2 / (N:ℝ) / (2 ^ N * 2 ^ (N * (d - 1))) * (L * Bsum) :=
            mul_le_mul_of_nonneg_left hineq (by positivity)
        _ = L * (2 / (N:ℝ) / (2 ^ N * 2 ^ (N * (d - 1))) * Bsum) := by ring

end L5

section L6
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {d N : ℕ}

theorem signedSup_meas (F : Set (X → Fin d → ℝ)) (hFm : ∀ f ∈ F, Measurable f)
    (hFs : IsPointwiseSeparable F) (σ : Fin N → Fin d → Bool) :
    Measurable (fun s : Fin N → X => signedSup F s σ) := by
  obtain ⟨F0, hF0G, hF0c, hF0⟩ := hFs
  have heq : ∀ s : Fin N → X, signedSup F s σ = ⨆ g ∈ F0,
      ((∑ i, ∑ k, signOf (σ i k) * g (s i) k : ℝ) : EReal) := by
    intro s
    unfold signedSup
    apply le_antisymm
    · refine iSup₂_le fun g hg => ?_
      obtain ⟨u, hu, hlim⟩ := hF0 g hg
      have ht : Tendsto (fun n => ((∑ i, ∑ k, signOf (σ i k) * u n (s i) k : ℝ) : EReal))
          atTop (𝓝 ((∑ i, ∑ k, signOf (σ i k) * g (s i) k : ℝ) : EReal)) := by
        refine (continuous_coe_real_ereal.tendsto _).comp ?_
        refine tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun k _ => ?_
        exact tendsto_const_nhds.mul (tendsto_pi_nhds.mp (hlim (s i)) k)
      refine le_of_tendsto ht (Eventually.of_forall fun n => ?_)
      exact le_iSup₂ (f := fun g (_ : g ∈ F0) =>
        ((∑ i, ∑ k, signOf (σ i k) * g (s i) k : ℝ) : EReal)) (u n) (hu n)
    · exact biSup_mono (fun g hg => hF0G hg)
  have : (fun s : Fin N → X => signedSup F s σ) = fun s => ⨆ g ∈ F0,
      ((∑ i, ∑ k, signOf (σ i k) * g (s i) k : ℝ) : EReal) := funext heq
  rw [this]
  refine Measurable.biSup F0 hF0c fun g hg => ?_
  refine continuous_coe_real_ereal.measurable.comp ?_
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun k _ => ?_
  have hgk : Measurable (fun u : X => g u k) := (measurable_pi_apply k).comp (hFm g (hF0G hg))
  exact (hgk.comp (measurable_pi_apply i)).const_mul _

theorem empRad_meas (F : Set (X → Fin d → ℝ)) (hFm : ∀ f ∈ F, Measurable f)
    (hFs : IsPointwiseSeparable F) :
    Measurable (fun s : Fin N → X => empRademacher F s) := by
  unfold empRademacher
  exact (Finset.measurable_sum _ fun σ _ => signedSup_meas F hFm hFs σ).const_mul _

theorem lemma1_ii (F : Set (X → Fin d → ℝ)) (c : (Fin d → ℝ) → Y → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hc_lip : ∀ (z z' : Fin d → ℝ) (y : Y), |c z y - c z' y| ≤ L * ‖z - z'‖)
    (μ : Measure (X × Y)) [IsProbabilityMeasure μ] (N : ℕ)
    (hFm : ∀ f ∈ F, Measurable f) (hFs : IsPointwiseSeparable F) :
    margRademacherR μ N (costClass c F) ≤
      ENNReal.ofReal L * margRademacher (μ.map Prod.fst) N F := by
  unfold margRademacherR margRademacher
  haveI : IsProbabilityMeasure (μ.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hmap : (Measure.pi fun _ : Fin N => μ).map (fun (s : Fin N → X × Y) i => (s i).1)
      = Measure.pi fun _ : Fin N => μ.map Prod.fst :=
    Measure.pi_map_pi (fun _ => measurable_fst.aemeasurable)
  have hgm : Measurable (fun (s : Fin N → X × Y) i => (s i).1) :=
    measurable_pi_lambda _ fun i => measurable_fst.comp (measurable_pi_apply i)
  have hφ : Measurable (fun t : Fin N → X => (empRademacher F t).toENNReal) :=
    (empRad_meas F hFm hFs).ereal_toENNReal
  calc ∫⁻ s, (empRademacher (liftClass (costClass c F)) s).toENNReal ∂(Measure.pi fun _ : Fin N => μ)
      ≤ ∫⁻ s, (ENNReal.ofReal L * (empRademacher F (fun i => (s i).1)).toENNReal)
          ∂(Measure.pi fun _ : Fin N => μ) := by
        refine lintegral_mono fun s => ?_
        have h := lemma1_i F c L hL hc_lip s
        have h2 := EReal.toENNReal_le_toENNReal h
        rw [EReal.toENNReal_mul (by exact_mod_cast hL)] at h2
        exact h2
    _ = ENNReal.ofReal L * ∫⁻ s, (empRademacher F (fun i => (s i).1)).toENNReal
          ∂(Measure.pi fun _ : Fin N => μ) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
        congr 1
        rw [← hmap, lintegral_map hφ hgm]

end L6
end PrescAnalytics.ERM

open PrescAnalytics.ERM
open MeasureTheory

theorem solution {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {d : ℕ}
    (F : Set (X → Fin d → ℝ)) (c : (Fin d → ℝ) → Y → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hc_lip : ∀ (z z' : Fin d → ℝ) (y : Y), |c z y - c z' y| ≤ L * ‖z - z'‖) :
    (∀ (N : ℕ) (s : Fin N → X × Y),
        empRademacherR (costClass c F) s ≤ (L : EReal) * empRademacher F (fun i => (s i).1)) ∧
    (∀ (μ : Measure (X × Y)) [IsProbabilityMeasure μ] (N : ℕ),
        (∀ f ∈ F, Measurable f) → IsPointwiseSeparable F → Measurable (Function.uncurry c) →
        margRademacherR μ N (costClass c F) ≤
          ENNReal.ofReal L * margRademacher (μ.map Prod.fst) N F) := by
  refine ⟨fun N s => lemma1_i F c L hL hc_lip s, ?_⟩
  intro μ _ N hFm hFs _
  exact lemma1_ii F c L hL hc_lip μ N hFm hFs
