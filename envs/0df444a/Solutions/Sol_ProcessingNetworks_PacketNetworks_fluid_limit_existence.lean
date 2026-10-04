-- Prove2me | solution 1 for ProcessingNetworks.PacketNetworks.fluid_limit_existence
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:25:56.366887+00:00
-- url     : https://prove2.me/submissions/af1e5a96-1ee1-40ec-babd-484d18d67289

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_ProcessesAndFluidModel

open Filter

namespace ProcessingNetworks.PacketNetworks.FLECE

open ProcessingNetworks.PacketNetworks

def dat : PacketNetworkData 1 1 := ⟨id, fun _ => none⟩

def P : PacketPrimitives 1 1 Unit := ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩

theorem state_const (z : Fin 1 → ℕ) (τ : ℕ) (ω : Unit) :
    policyState dat P z τ ω = fun i => (z i : ℤ) := by
  induction τ with
  | zero => rfl
  | succ τ ih =>
    simp only [policyState, ih]
    funext i
    simp [nextState, P]

theorem sched (z : Fin 1 → ℕ) (τ : ℕ) (ω : Unit) : policySched dat P z τ ω = 0 := rfl

theorem T_eq (z : Fin 1 → ℕ) (τ : ℕ) (ω : Unit) : Tproc dat P z 0 τ ω = τ := by
  unfold Tproc
  rw [Finset.filter_true_of_mem (fun ℓ _ => sched z ℓ ω)]
  simp

theorem D_eq (z : Fin 1 → ℕ) (τ : ℕ) (ω : Unit) : Dproc dat P z τ ω = 0 := by
  funext j; simp [Dproc, sched]

theorem Z_eq (z : Fin 1 → ℕ) (τ : ℕ) (ω : Unit) : Zproc dat P z τ ω = fun i => (z i : ℝ) := by
  funext i; simp [Zproc, state_const]

noncomputable def zseq (n : ℕ) : Fin 1 → ℕ := fun _ => n + 1

theorem size_eq (n : ℕ) : sizeN (zseq n) = (n : ℝ) + 1 := by
  simp [sizeN, zseq]

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

theorem conv : FluidScaledConverge dat P {0} () zseq (fun _ _ => 0) (fun t _ => |t|)
    (fun _ _ => 1) := by
  refine ⟨fun Tb _ ε hε => ⟨0, fun n _ t _ i => ?_⟩, fun Tb _ ε hε => ?_,
    fun Tb _ ε hε => ⟨0, fun n _ t _ i => ?_⟩⟩
  · simp [D_eq, hε]
  · obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, fun n hn t ht s hs => ?_⟩
    rw [Finset.mem_singleton] at hs
    subst hs
    simp only [T_eq, size_eq, abs_of_nonneg ht.1]
    refine lt_of_le_of_lt (floor_approx n t ht.1) (lt_of_le_of_lt ?_ hN)
    rw [one_div]
    exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
  · beta_reduce
    rw [Z_eq, size_eq]
    have : ((n : ℝ) + 1)⁻¹ * (zseq n i : ℝ) = 1 := by
      simp only [zseq]; push_cast; field_simp
    rw [this, sub_self, abs_zero]; exact hε

end ProcessingNetworks.PacketNetworks.FLECE

open ProcessingNetworks.PacketNetworks in
theorem solution : ¬ (∀ {I J : ℕ} {Ω : Type} (dat : PacketNetworkData I J) (S : Finset (Fin J → ℕ))
    (P : PacketPrimitives I J Ω) (hadm : IsAdmissibleMarkovianPolicy dat S P.f)
    (lam : Fin I → ℝ) (ω : Ω) (hω : SLLNHoldsAt P lam ω)
    (G : Set (Fin I → ℕ)) (hG : ¬ BddAbove (sizeN '' G)),
    (∃ zseq : ℕ → Fin I → ℕ, (∀ n, zseq n ∈ G) ∧ Tendsto (fun n => sizeN (zseq n)) atTop atTop ∧
      ∃ (Dh : ℝ → Fin J → ℝ) (Th : ℝ → (Fin J → ℕ) → ℝ) (Zh : ℝ → Fin I → ℝ),
        FluidScaledConverge dat P S ω zseq Dh Th Zh) ∧
    ∀ (zseq : ℕ → Fin I → ℕ) (Dh : ℝ → Fin J → ℝ) (Th : ℝ → (Fin J → ℕ) → ℝ)
      (Zh : ℝ → Fin I → ℝ), (∀ n, zseq n ∈ G) → Tendsto (fun n => sizeN (zseq n)) atTop atTop →
      FluidScaledConverge dat P S ω zseq Dh Th Zh →
      SatisfiesPacketFluidEquations dat S lam Dh Th Zh) := by
  intro h
  have hadm : IsAdmissibleMarkovianPolicy FLECE.dat {0} FLECE.P.f := fun z u _ _ =>
    ⟨Finset.mem_singleton_self _, fun i => by
      have : (fun j => ((FLECE.P.f z u j : ℕ) : ℝ)) = 0 := funext fun j => by simp [FLECE.P]
      rw [this, Matrix.mulVec_zero]
      exact Nat.cast_nonneg _⟩
  have hω : SLLNHoldsAt FLECE.P 0 () := fun M _ ε hε => ⟨0, fun _ _ t _ i => by
    simp [Ecum, FLECE.P, hε]⟩
  have hG : ¬ BddAbove (sizeN '' (Set.univ : Set (Fin 1 → ℕ))) := by
    rintro ⟨b, hb⟩
    obtain ⟨n, hn⟩ := exists_nat_gt b
    have := hb ⟨FLECE.zseq n, Set.mem_univ _, rfl⟩
    rw [FLECE.size_eq] at this
    linarith
  have htend : Tendsto (fun n => sizeN (FLECE.zseq n)) atTop atTop := by
    simp only [FLECE.size_eq]
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have := (h FLECE.dat {0} FLECE.P hadm 0 () hω Set.univ hG).2 FLECE.zseq _ _ _
    (fun _ => Set.mem_univ _) htend FLECE.conv
  obtain ⟨-, -, -, -, -, ⟨hmono, -⟩⟩ := this
  have := hmono 0 (Finset.mem_singleton_self _) (show (-1 : ℝ) ≤ 0 by norm_num)
  norm_num at this


