-- Prove2me | solution 1 for QCQPTightness.Sharp.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:52:24.251349+00:00
-- url     : https://prove2.me/submissions/50cb0858-5f79-48e9-ab7b-fec8a8d70d41

import Mathlib
import Definitions.Def_QCQPTightness_Sharp_QCQP
import Definitions.Def_QCQPTightness_Sharp_Faces
import Definitions.Def_QCQPTightness_Sharp_Mult

namespace RRAux_QCQPTightness_Sharp_proposition_2

open Matrix QCQPTightness.ConvHull

lemma quad_diag {N : ℕ} (a b x : Fin N → ℝ) (c : ℝ) :
    quad (diagonal a) b c x = ∑ i, a i * x i ^ 2 + 2 * (b ⬝ᵥ x) + c := by
  simp only [quad]
  congr 2
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma quad_zero {N : ℕ} (b x : Fin N → ℝ) (c : ℝ) :
    quad 0 b c x = 2 * (b ⬝ᵥ x) + c := by
  simp [quad]

lemma trace_zero {N : ℕ} (b x : Fin N → ℝ) (c : ℝ) (X : Matrix (Fin N) (Fin N) ℝ) :
    (liftQ 0 b c * liftY x X).trace = 2 * (b ⬝ᵥ x) + c := by
  simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_sum_type, liftQ, liftY, dotProduct,
    Matrix.fromBlocks, Finset.sum_add_distrib]
  ring

lemma trace_diag {N : ℕ} (a b x : Fin N → ℝ) (c : ℝ) (X : Matrix (Fin N) (Fin N) ℝ) :
    (liftQ (diagonal a) b c * liftY x X).trace = ∑ j, a j * X j j + 2 * (b ⬝ᵥ x) + c := by
  simp [Matrix.trace, Matrix.mul_apply, Fintype.sum_sum_type, liftQ, liftY, dotProduct,
    diagonal_apply, Matrix.fromBlocks, ite_mul, Finset.sum_add_distrib]
  ring

lemma blockEquiv_val {k n N : ℕ} (h : k * n = N) (p : Fin k × Fin n) :
    ((QCQPTightness.Sharp.blockEquiv h p : Fin N) : ℕ) = p.2 + n * p.1 := by
  simp [QCQPTightness.Sharp.blockEquiv, finProdFinEquiv_apply_val]

variable (n k : ℕ)

def E : Fin k × Fin n ≃ Fin (n * k) := QCQPTightness.Sharp.blockEquiv (Nat.mul_comm k n)

def sOf (idx : Fin (n * k)) : Fin n := ((E n k).symm idx).2

lemma sOf_val (idx : Fin (n * k)) : ((sOf n k idx : Fin n) : ℕ) = (idx : ℕ) % n := by
  simp [sOf, E, QCQPTightness.Sharp.blockEquiv, finProdFinEquiv_symm_apply, Fin.coe_modNat]

lemma sOf_E (p : Fin k × Fin n) : sOf n k (E n k p) = p.2 := by simp [sOf]

def d (idx : Fin (n * k)) : ℝ := ((sOf n k idx : Fin n) : ℕ)

def z (idx : Fin (n * k)) : ℝ := if ((sOf n k idx : Fin n) : ℕ) = 0 then 1 else 0

lemma d_nonneg (idx : Fin (n * k)) : 0 ≤ d n k idx := by simp [d]

lemma z_nonneg (idx : Fin (n * k)) : 0 ≤ z n k idx := by unfold z; split_ifs <;> norm_num

lemma d_add_z_pos (idx : Fin (n * k)) : 0 < d n k idx + z n k idx := by
  unfold d z
  split_ifs with h
  · rw [h]; norm_num
  · have : (1 : ℝ) ≤ ((sOf n k idx : Fin n) : ℕ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    linarith

variable {n k} (hn : 0 < n) (hk : 0 < k)

def i0 : Fin (n * k) := E n k (⟨0, hk⟩, ⟨0, hn⟩)

def blk (i : ℕ) : Fin k := ⟨i % k, Nat.mod_lt _ hk⟩

lemma d_i0 : d n k (i0 hn hk) = 0 := by simp [d, i0, sOf_E]
lemma z_i0 : z n k (i0 hn hk) = 1 := by simp [z, i0, sOf_E]

noncomputable def P : QCQPTightness.Sharp.QCQP (n * k) (k + 1) where
  A₀ := diagonal (d n k)
  b₀ := Pi.single (i0 hn hk) 1
  c₀ := 0
  A i := diagonal (fun idx => if (i : ℕ) = k then z n k idx else 0)
  b i := if (i : ℕ) = 0 then (-(1 / 2 : ℝ)) • Pi.single (i0 hn hk) 1
    else if (i : ℕ) < k then Pi.single (E n k (blk hk i, ⟨0, hn⟩)) 1 else 0
  c i := if (i : ℕ) = 0 then -(1 / 2) else if (i : ℕ) = k then -1 else 0
  mI := 1
  mI_le := by omega
  A₀_symm := isSymm_diagonal _
  A_symm _ := isSymm_diagonal _

lemma cases3 (i : Fin (k + 1)) :
    (i : ℕ) = 0 ∨ (0 < (i : ℕ) ∧ (i : ℕ) < k) ∨ (i : ℕ) = k := by omega

lemma E_inj_i0 (j : Fin k) (hj : (j : ℕ) ≠ 0) : E n k (j, ⟨0, hn⟩) ≠ i0 hn hk := by
  intro h
  apply hj
  have := (E n k).injective h
  simp only [Prod.mk.injEq] at this
  rw [this.1]

lemma sum_z (x : Fin (n * k) → ℝ) (hx : ∀ j : Fin k, (j : ℕ) ≠ 0 → x (E n k (j, ⟨0, hn⟩)) = 0) :
    ∑ idx, z n k idx * x idx ^ 2 = x (i0 hn hk) ^ 2 := by
  rw [← Equiv.sum_comp (E n k), Fintype.sum_prod_type]
  simp only [z, sOf_E]
  rw [Finset.sum_eq_single (⟨0, hk⟩ : Fin k)]
  · rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
    · simp [i0]
    · intro s _ hs
      have : (s : ℕ) ≠ 0 := fun h => hs (Fin.ext h)
      simp [this]
    · simp
  · intro j _ hj
    have hj' : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs with hs
    · have : s = ⟨0, hn⟩ := Fin.ext hs
      subst this
      simp [hx j hj']
    · simp
  · simp

lemma blk_eq (j : ℕ) (hj : j < k) : blk hk j = ⟨j, hj⟩ := Fin.ext (Nat.mod_eq_of_lt hj)

-- the feasible set forces x_{i0} = 1, so q₀ ≥ 2
lemma feasible_ge (x : Fin (n * k) → ℝ) (hx : x ∈ (P hn hk).feasible) : 2 ≤ (P hn hk).q₀ x := by
  have h0 := (hx ⟨0, by omega⟩).1 (by show (0 : ℕ) < 1; omega)
  have hlast := (hx (Fin.last k)).2 (by show ¬ (k < 1); omega)
  have hj : ∀ j : Fin k, (j : ℕ) ≠ 0 → x (E n k (j, ⟨0, hn⟩)) = 0 := by
    intro j hj
    have := (hx ⟨j, by omega⟩).2 (by show ¬ ((j : ℕ) < 1); omega)
    have hjk : (j : ℕ) ≠ k := by omega
    simp [QCQPTightness.Sharp.QCQP.q, P, quad_zero, hj, hjk, j.2, blk_eq hk j j.2] at this
    simpa using this
  have hk0 : k ≠ 0 := by omega
  have hk0' : (0 : ℕ) ≠ k := Ne.symm hk0
  simp [QCQPTightness.Sharp.QCQP.q, P, quad_diag, quad_zero, hk0, hk0'] at h0 hlast
  rw [sum_z hn hk x hj] at hlast
  have hx1 : x (i0 hn hk) = 1 := by nlinarith
  simp only [QCQPTightness.Sharp.QCQP.q₀, P, quad_diag]
  have : 0 ≤ ∑ i, d n k i * x i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (d_nonneg n k i) (sq_nonneg _)
  simp [hx1]
  linarith

noncomputable def xs : Fin (n * k) → ℝ := (-(1 / 2 : ℝ)) • Pi.single (i0 hn hk) 1

def Xs : Matrix (Fin (n * k)) (Fin (n * k)) ℝ := diagonal (Pi.single (i0 hn hk) 1)

lemma Ys_psd : (liftY (xs hn hk) (Xs hn hk)).PosSemidef := by
  have e : liftY (xs hn hk) (Xs hn hk) =
      vecMulVec (Sum.elim (fun _ : Fin 1 => (1:ℝ)) (xs hn hk))
        (star (Sum.elim (fun _ : Fin 1 => (1:ℝ)) (xs hn hk)))
      + diagonal (Sum.elim (fun _ : Fin 1 => (0:ℝ)) (Pi.single (i0 hn hk) (3 / 4))) := by
    ext (i | i) (j | j) <;>
      simp [liftY, Matrix.fromBlocks, xs, Xs, vecMulVec_apply, diagonal_apply, Pi.single_apply] <;>
      split_ifs <;> simp_all <;> norm_num
  rw [e]
  refine (posSemidef_vecMulVec_self_star _).add (PosSemidef.diagonal ?_)
  intro i
  rcases i with i | i
  · simp
  · simp [Pi.single_apply]; split_ifs <;> norm_num

lemma sdp_feasible : (xs hn hk, Xs hn hk) ∈ (P hn hk).sdpFeasible := by
  refine ⟨isSymm_diagonal _, Ys_psd hn hk, fun i => ?_⟩
  have hk0 : k ≠ 0 := by omega
  rcases cases3 i with h | ⟨h1, h2⟩ | h
  · have hiF : i = 0 := Fin.ext (by simp [h])
    have hk0' : (0 : ℕ) ≠ k := Ne.symm hk0
    refine ⟨fun _ => ?_, fun hc => absurd (show (i : ℕ) < 1 by omega) hc⟩
    simp [P, trace_diag, trace_zero, hiF, hk0', xs, Xs, dotProduct, Pi.single_apply]
  · have hik : (i : ℕ) ≠ k := by omega
    have hi0 : (i : ℕ) ≠ 0 := by omega
    refine ⟨fun hc => absurd hc (show ¬ ((i : ℕ) < 1) by omega), fun _ => ?_⟩
    have hne := E_inj_i0 hn hk (blk hk i) (by rw [blk_eq hk i h2]; exact hi0)
    have hiF : i ≠ 0 := fun hh => hi0 (by simp [hh])
    simp [P, trace_diag, trace_zero, hik, hiF, h2, xs, Xs, dotProduct, Pi.single_apply, hne, Ne.symm hne]
  · have hi0 : (i : ℕ) ≠ 0 := by omega
    have hlt : ¬ ((i : ℕ) < k) := by omega
    refine ⟨fun hc => absurd hc (show ¬ ((i : ℕ) < 1) by omega), fun _ => ?_⟩
    have hiF : i ≠ 0 := fun hh => hi0 (by simp [hh])
    simp [P, trace_diag, h, hiF, xs, Xs, Pi.single_apply, z_i0]

lemma sdp_value :
    (liftQ (P hn hk).A₀ (P hn hk).b₀ (P hn hk).c₀ * liftY (xs hn hk) (Xs hn hk)).trace = -1 := by
  simp [P, trace_diag, xs, Xs, Pi.single_apply, d_i0, dotProduct]

lemma Aγ_eq (γ : Fin (k + 1) → ℝ) :
    (P hn hk).Aγ γ = diagonal (fun idx => d n k idx + γ (Fin.last k) * z n k idx) := by
  ext a b
  simp only [QCQPTightness.Sharp.QCQP.Aγ, P, Matrix.add_apply, Matrix.sum_apply,
    Matrix.smul_apply, diagonal_apply, smul_eq_mul]
  split_ifs with hab
  · rw [Finset.sum_eq_single (Fin.last k)]
    · simp
    · intro i _ hi
      have : (i : ℕ) ≠ k := fun h => hi (Fin.ext h)
      simp [this]
    · simp
  · simp

lemma gamma_iff (γ : Fin (k + 1) → ℝ) :
    γ ∈ (P hn hk).Gamma ↔ 0 ≤ γ 0 ∧ 0 ≤ γ (Fin.last k) := by
  rw [show γ ∈ (P hn hk).Gamma ↔ ((P hn hk).Aγ γ).PosSemidef ∧
      ∀ i, (P hn hk).IsIneq i → 0 ≤ γ i from Iff.rfl, Aγ_eq, posSemidef_diagonal_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2 0 (by show ((0 : Fin (k + 1)) : ℕ) < 1; simp), ?_⟩
    have := h1 (i0 hn hk)
    simpa [d_i0, z_i0] using this
  · rintro ⟨h1, h2⟩
    refine ⟨fun idx => add_nonneg (d_nonneg n k idx) (mul_nonneg h2 (z_nonneg n k idx)),
      fun i hi => ?_⟩
    have hi' : (i : ℕ) < 1 := hi
    have : i = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
    rw [this]; exact h1

lemma kron_diag (f : Fin n → ℝ) :
    Matrix.reindex (QCQPTightness.Sharp.blockEquiv (Nat.mul_comm k n))
      (QCQPTightness.Sharp.blockEquiv (Nat.mul_comm k n)) (QCQPTightness.Sharp.kronId k (diagonal f))
      = diagonal (fun idx => f (sOf n k idx)) := by
  rw [QCQPTightness.Sharp.kronId, ← diagonal_one, diagonal_kronecker_diagonal, reindex_apply,
    submatrix_diagonal_equiv]
  congr 1
  funext idx
  simp [sOf, E]

lemma hasMult : (P hn hk).HasMultiplicity k := by
  refine ⟨n, Nat.mul_comm k n, ⟨diagonal (fun s => ((s : ℕ) : ℝ)), isSymm_diagonal _, ?_⟩,
    fun i => ⟨diagonal (fun s => if (i : ℕ) = k then (if (s : ℕ) = 0 then 1 else 0) else 0),
      isSymm_diagonal _, ?_⟩⟩
  · rw [kron_diag]; rfl
  · rw [kron_diag]; rfl

lemma mult_le (k' : ℕ) (hk' : (P hn hk).HasMultiplicity k') : k' ≤ k := by
  by_contra hlt
  push Not at hlt
  obtain ⟨n', h', ⟨𝔸, _, hA⟩, _⟩ := hk'
  have hpos : 0 < n * k := Nat.mul_pos hn hk
  have hn'0 : 0 < n' := by
    rcases Nat.eq_zero_or_pos n' with h | h
    · rw [h] at h'; omega
    · exact h
  have hn'n : n' < n := by
    by_contra hc; push Not at hc
    have : k * n < k' * n' := by
      calc k * n < k' * n := Nat.mul_lt_mul_of_pos_right hlt hn
        _ ≤ k' * n' := Nat.mul_le_mul_left k' hc
    rw [h', Nat.mul_comm] at this; omega
  have hk'2 : 1 < k' := by omega
  set E' := QCQPTightness.Sharp.blockEquiv h' with hE'
  have key : ∀ j : Fin k', (P hn hk).A₀ (E' (j, ⟨0, hn'0⟩)) (E' (j, ⟨0, hn'0⟩)) = 𝔸 ⟨0, hn'0⟩ ⟨0, hn'0⟩ := by
    intro j
    rw [hA]
    simp [reindex_apply, QCQPTightness.Sharp.kronId, kroneckerMap_apply]
  have k0 := key ⟨0, by omega⟩
  have k1 := key ⟨1, hk'2⟩
  rw [← k1] at k0
  simp only [P, diagonal_apply_eq, d, sOf_val, hE', blockEquiv_val] at k0
  simp at k0
  rw [Nat.mod_eq_of_lt hn'n] at k0
  norm_cast at k0
  omega

lemma affdim_le (F : Set (Fin (k + 1) → ℝ)) :
    QCQPTightness.Sharp.affdim ((P hn hk).bγ '' F) ≤ k := by
  let bl : Fin k → (Fin (n * k) → ℝ) := fun j => (P hn hk).b (Fin.castSucc j)
  have hsub : vectorSpan ℝ ((P hn hk).bγ '' F) ≤ Submodule.span ℝ (Set.range bl) := by
    rw [vectorSpan_def]
    refine Submodule.span_le.mpr ?_
    rintro v ⟨u, ⟨γ, _, rfl⟩, w, ⟨γ', _, rfl⟩, rfl⟩
    have hlast : (P hn hk).b (Fin.last k) = 0 := by
      have : ¬ (k < k) := lt_irrefl k
      have hk0 : k ≠ 0 := by omega
      simp [P, this, hk0]
    have : (P hn hk).bγ γ -ᵥ (P hn hk).bγ γ' = ∑ j : Fin k, (γ (Fin.castSucc j) - γ' (Fin.castSucc j)) • bl j := by
      simp only [vsub_eq_sub, QCQPTightness.Sharp.QCQP.bγ]
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, hlast]
      simp only [smul_zero, add_zero, bl, sub_smul, Finset.sum_sub_distrib]
      abel
    change (P hn hk).bγ γ -ᵥ (P hn hk).bγ γ' ∈ _
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  unfold QCQPTightness.Sharp.affdim
  calc Module.finrank ℝ (vectorSpan ℝ ((P hn hk).bγ '' F))
      ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range bl)) := Submodule.finrank_mono hsub
    _ ≤ Fintype.card (Fin k) := finrank_range_le_card bl
    _ = k := Fintype.card_fin k

end RRAux_QCQPTightness_Sharp_proposition_2

open RRAux_QCQPTightness_Sharp_proposition_2 in
open QCQPTightness.Sharp in
theorem solution : ∀ n k : ℕ, 0 < n → 0 < k →
    ∃ P : QCQP (n * k) (k + 1),
      P.Assumption1 ∧ P.Assumption3 ∧ P.IsQuadEigMult k ∧
      (∀ F : Set (Fin (k + 1) → ℝ), P.IsSemidefiniteFace F → affdim (P.bγ '' F) ≤ k) ∧
      P.Opt ≠ P.OptSDP ∧ convexHull ℝ P.D ≠ P.DSDP := by
  intro n k hn hk
  refine ⟨P hn hk, ?_, ?_, ⟨hasMult hn hk, fun k' hk' => mult_le hn hk k' hk'⟩,
    fun F _ => affdim_le hn hk F, ?_, ?_⟩
  · -- Assumption 1
    refine ⟨⟨Pi.single (i0 hn hk) 1, ?_⟩, Pi.single (Fin.last k) 1, ?_, ?_⟩
    · intro i
      have hk0 : k ≠ 0 := by omega
      rcases cases3 i with h | ⟨h1, h2⟩ | h
      · have hiF : i = 0 := Fin.ext (by simp [h])
        have hk0' : (0 : ℕ) ≠ k := Ne.symm hk0
        refine ⟨fun _ => ?_, fun hc => absurd (show (i : ℕ) < 1 by omega) hc⟩
        simp [QCQP.q, P, quad_diag, quad_zero, hiF, hk0', dotProduct, Pi.single_apply]
        norm_num
      · have hik : (i : ℕ) ≠ k := by omega
        have hi0 : (i : ℕ) ≠ 0 := by omega
        have hiF : i ≠ 0 := fun hh => hi0 (by simp [hh])
        refine ⟨fun hc => absurd hc (show ¬ ((i : ℕ) < 1) by omega), fun _ => ?_⟩
        have hne := E_inj_i0 hn hk (blk hk i) (by rw [blk_eq hk i h2]; exact hi0)
        simp [QCQP.q, P, quad_zero, hik, hiF, h2, dotProduct, Pi.single_apply, hne, Ne.symm hne]
      · have hi0 : (i : ℕ) ≠ 0 := by omega
        have hiF : i ≠ 0 := fun hh => hi0 (by simp [hh])
        refine ⟨fun hc => absurd hc (show ¬ ((i : ℕ) < 1) by omega), fun _ => ?_⟩
        simp [QCQP.q, P, quad_diag, h, hiF, Pi.single_apply, z_i0]
    · intro i hi
      simp [Pi.single_apply]
      split_ifs <;> norm_num
    · rw [Aγ_eq, Matrix.posDef_diagonal_iff]
      intro idx
      simpa using d_add_z_pos n k idx
  · -- Assumption 3
    refine ⟨2, ![-(Pi.single 0 1), -(Pi.single (Fin.last k) 1)], ![0, 0], ?_⟩
    ext γ
    rw [gamma_iff]
    simp [Fin.forall_fin_two, dotProduct, Pi.single_apply]
  · -- Opt ≠ Opt_SDP
    have h1 : ((2 : ℝ) : EReal) ≤ (P hn hk).Opt :=
      le_iInf₂ fun x hx => EReal.coe_le_coe_iff.mpr (feasible_ge hn hk x hx)
    have h2 : (P hn hk).OptSDP ≤ ((-1 : ℝ) : EReal) := by
      refine iInf₂_le_of_le (xs hn hk, Xs hn hk) (sdp_feasible hn hk) (le_of_eq ?_)
      rw [sdp_value]
    intro heq
    rw [heq] at h1
    have : ((2 : ℝ) : EReal) ≤ ((-1 : ℝ) : EReal) := h1.trans h2
    have : (2 : ℝ) ≤ -1 := EReal.coe_le_coe_iff.mp this
    norm_num at this
  · -- conv 𝒟 ≠ 𝒟_SDP
    intro heq
    have hmem : (xs hn hk, (-(1 / 2) : ℝ)) ∈ (P hn hk).DSDP :=
      ⟨Xs hn hk, sdp_feasible hn hk, by rw [sdp_value]; norm_num⟩
    rw [← heq] at hmem
    have hsub : (P hn hk).D ⊆ {p | (1 : ℝ) ≤ p.2} := by
      intro p hp
      have := feasible_ge hn hk p.1 hp.2
      show (1 : ℝ) ≤ p.2
      linarith [hp.1]
    have hconv : Convex ℝ {p : (Fin (n * k) → ℝ) × ℝ | (1 : ℝ) ≤ p.2} := by
      intro p hp q hq a b ha hb hab
      show (1 : ℝ) ≤ (a • p + b • q).2
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      have hp' : (1 : ℝ) ≤ p.2 := hp
      have hq' : (1 : ℝ) ≤ q.2 := hq
      nlinarith
    have := convexHull_min hsub hconv hmem
    norm_num at this

#print axioms solution
