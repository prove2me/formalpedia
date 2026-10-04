-- Prove2me | solution 1 for ProcessingNetworks.PacketNetworks.back_pressure_fluid_equation
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:29:27.147398+00:00
-- url     : https://prove2.me/submissions/e21c1fc9-4671-4779-bea1-328e8936a0ee

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_BackPressurePolicy
import Definitions.Def_ProcessingNetworks_PacketNetworks_BPFluidModel

open Filter

namespace ProcessingNetworks.PacketNetworks.BPFECE

open ProcessingNetworks.PacketNetworks

def dat : PacketNetworkData 2 2 := ⟨id, fun _ => none⟩

def one2 : Fin 2 → ℕ := fun _ => 1

def S : Finset (Fin 2 → ℕ) := {0, one2}

def f (z : Fin 2 → ℕ) (_ : ℝ) : Fin 2 → ℕ := if 1 ≤ z 0 ∧ 1 ≤ z 1 then one2 else 0

noncomputable def P : PacketPrimitives 2 2 Unit := ⟨f, fun _ _ => 0, fun _ _ => 1 / 2⟩

theorem R_eq : R dat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [R, dat]

theorem B_eq : B dat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [B, dat]

theorem obj (z : Fin 2 → ℝ) (s : Fin 2 → ℕ) : bpObjective dat z s = z 0 * s 0 + z 1 * s 1 := by
  simp [bpObjective, R_eq, dotProduct, Fin.sum_univ_two, realize]

theorem feas (z : Fin 2 → ℝ) (s : Fin 2 → ℕ) :
    s ∈ feasibleSchedulesAt dat S z ↔ s ∈ S ∧ (s 0 : ℝ) ≤ z 0 ∧ (s 1 : ℝ) ≤ z 1 := by
  simp [feasibleSchedulesAt, B_eq, Fin.forall_fin_two, realize]

theorem hBP : IsBackPressurePolicy dat S P.f := by
  intro z uu _ _
  have hz0 : (0 : ℝ) ≤ z 0 := Nat.cast_nonneg _
  have hz1 : (0 : ℝ) ≤ z 1 := Nat.cast_nonneg _
  by_cases h : 1 ≤ z 0 ∧ 1 ≤ z 1
  · have hf : P.f z uu = one2 := if_pos h
    rw [hf]
    refine ⟨(feas _ _).mpr ⟨by simp [S], by simp [one2]; exact_mod_cast h.1,
      by simp [one2]; exact_mod_cast h.2⟩, fun s' hs' => ?_⟩
    rw [feas] at hs'
    rcases hs' with ⟨hs, -, -⟩
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · rw [obj, obj]; simp [one2]; linarith
    · exact le_refl _
  · have hf : P.f z uu = 0 := if_neg h
    rw [hf]
    refine ⟨(feas _ _).mpr ⟨by simp [S], by simpa using hz0, by simpa using hz1⟩,
      fun s' hs' => ?_⟩
    rw [feas] at hs'
    rcases hs' with ⟨hs, h0, h1⟩
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact le_refl _
    · exfalso; apply h
      simp only [one2, Nat.cast_one] at h0 h1
      exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩

noncomputable def zseq (n : ℕ) : Fin 2 → ℕ := ![n + 1, 0]

theorem state_const (n τ : ℕ) : policyState dat P (zseq n) τ () = fun i => (zseq n i : ℤ) := by
  induction τ with
  | zero => rfl
  | succ τ ih =>
    simp only [policyState, ih]
    have : P.f (fun i => ((zseq n i : ℤ)).toNat) (P.U (τ + 1) ()) = 0 := by
      simp only [P]
      simp [f, zseq]
    rw [this]
    funext i
    simp [nextState, P]

theorem sched (n τ : ℕ) (hτ : 1 ≤ τ) : policySched dat P (zseq n) τ () = 0 := by
  unfold policySched
  rw [state_const]
  simp only [P]
  simp [f, zseq]

theorem T0 (n τ : ℕ) : Tproc dat P (zseq n) 0 τ () = τ := by
  unfold Tproc
  rw [Finset.filter_true_of_mem (fun ℓ hℓ => sched n ℓ (Finset.mem_Icc.mp hℓ).1)]
  simp

theorem T1 (n τ : ℕ) : Tproc dat P (zseq n) one2 τ () = 0 := by
  unfold Tproc
  rw [Finset.filter_false_of_mem (fun ℓ hℓ => by
    rw [sched n ℓ (Finset.mem_Icc.mp hℓ).1]
    intro h; have := congrFun h 0; simp [one2] at this)]
  simp

theorem D_eq (n τ : ℕ) : Dproc dat P (zseq n) τ () = 0 := by
  funext j
  simp only [Dproc]
  rw [Finset.sum_eq_zero (fun ℓ hℓ => by rw [sched n ℓ (Finset.mem_Icc.mp hℓ).1]; simp)]
  rfl

theorem Z_eq (n τ : ℕ) : Zproc dat P (zseq n) τ () = fun i => (zseq n i : ℝ) := by
  funext i; simp [Zproc, state_const]

theorem size_eq (n : ℕ) : sizeN (zseq n) = (n : ℝ) + 1 := by
  simp [sizeN, zseq, Fin.sum_univ_two]

theorem floor_approx (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    |((n : ℝ) + 1)⁻¹ * (⌊((n : ℝ) + 1) * t⌋₊ : ℝ) - t| ≤ ((n : ℝ) + 1)⁻¹ := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 := Nat.floor_le (show 0 ≤ ((n : ℝ) + 1) * t by positivity)
  have h2 := Nat.lt_floor_add_one (((n : ℝ) + 1) * t)
  have key : ((n : ℝ) + 1)⁻¹ * (⌊((n : ℝ) + 1) * t⌋₊ : ℝ) - t =
      ((⌊((n : ℝ) + 1) * t⌋₊ : ℝ) - ((n : ℝ) + 1) * t) * ((n : ℝ) + 1)⁻¹ := by
    field_simp
  rw [key, abs_mul, abs_of_pos (inv_pos.mpr hn)]
  exact mul_le_of_le_one_left (inv_nonneg.mpr hn.le) (abs_le.mpr ⟨by linarith, by linarith⟩)

noncomputable def Th (t : ℝ) (s : Fin 2 → ℕ) : ℝ := if s = 0 then t else 0

noncomputable def Zh (_ : ℝ) : Fin 2 → ℝ := ![1, 0]

theorem path : IsFluidLimitPath dat P S 0 (fun _ _ => 0) Th Zh := by
  refine ⟨(), zseq, fun M _ ε hε => ⟨0, fun _ _ t _ i => by simp [Ecum, P, hε]⟩, ?_, ?_, ?_, ?_⟩
  · simp only [size_eq]
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  · exact fun Tb _ ε hε => ⟨0, fun n _ t _ i => by simp [D_eq, hε]⟩
  · intro Tb _ ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, fun n hn t ht s hs => ?_⟩
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · simp only [T0, size_eq, Th, if_pos rfl]
      refine lt_of_le_of_lt (floor_approx n t ht.1) (lt_of_le_of_lt ?_ hN)
      rw [one_div]
      exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
    · have hne : one2 ≠ 0 := by intro h; have := congrFun h 0; simp [one2] at this
      simp only [T1, Th, if_neg hne, Nat.cast_zero, mul_zero, sub_zero, abs_zero]
      exact hε
  · intro Tb _ ε hε
    refine ⟨0, fun n _ t _ i => ?_⟩
    beta_reduce
    rw [Z_eq, size_eq]
    fin_cases i
    · have : ((n : ℝ) + 1)⁻¹ * (zseq n 0 : ℝ) = 1 := by
        simp only [zseq]; simp; field_simp
      simp only [Fin.zero_eta] at this ⊢
      rw [this]; simp [Zh, hε]
    · simp [zseq, Zh, hε]

end ProcessingNetworks.PacketNetworks.BPFECE

open ProcessingNetworks.PacketNetworks in
theorem solution : ¬ (∀ {I J : ℕ} {Ω : Type} (dat : PacketNetworkData I J) (S : Finset (Fin J → ℕ))
    (P : PacketPrimitives I J Ω) (hBP : IsBackPressurePolicy dat S P.f) (lam : Fin I → ℝ)
    (Dh : ℝ → Fin J → ℝ) (Th : ℝ → (Fin J → ℕ) → ℝ) (Zh : ℝ → Fin I → ℝ)
    (hFL : IsFluidLimitPath dat P S lam Dh Th Zh),
    SatisfiesBackPressureFluidEquation dat S Dh Th Zh) := by
  intro h
  have key := h BPFECE.dat BPFECE.S BPFECE.P BPFECE.hBP 0 _ _ _ BPFECE.path 1 zero_le_one
    ⟨differentiableWithinAt_const _, fun s _ => by
      unfold BPFECE.Th; split_ifs
      · exact differentiableWithinAt_id
      · exact differentiableWithinAt_const _,
      differentiableWithinAt_const _⟩ 0 (hasDerivWithinAt_const _ _ _)
  obtain ⟨shat, -, hdom, heq⟩ := key
  have hmem : realize BPFECE.one2 ∈ hullFinset BPFECE.S :=
    subset_convexHull ℝ _ ⟨BPFECE.one2, by simp [BPFECE.S], rfl⟩
  have := hdom _ hmem
  rw [← heq] at this
  simp [BPFECE.R_eq, BPFECE.Zh, dotProduct, Fin.sum_univ_two, realize, BPFECE.one2] at this
  norm_num at this


