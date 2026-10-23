-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P17.complex_schur_algebra
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T12:12:32.737124+00:00
-- url     : https://prove2.me/submissions/89e9cb57-4390-44e5-8480-2f49a15282e2

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P17

open scoped BigOperators Matrix.Norms.Elementwise

attribute [local instance 100] LieRing.ofAssociativeRing

section X8

variable {d : ℕ} {S : Type*} [AddCommGroup S] [Module ℂ S]

abbrev x8Q (d : ℕ) := cliffordQ (1 : Matrix (Fin d) (Fin d) ℂ)

theorem x8_Q_single (i : Fin d) : x8Q d (Pi.single i 1) = -1 := by
  simp [x8Q, cliffordQ, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply']

theorem x8_polar_single (i j : Fin d) (h : i ≠ j) :
    QuadraticMap.polar (x8Q d) (Pi.single i 1) (Pi.single j 1) = 0 := by
  simp [QuadraticMap.polar, x8Q, cliffordQ, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply',
    dotProduct, Pi.single_apply, Finset.sum_add_distrib, h, h.symm, add_mul, mul_add, Matrix.add_mulVec,
    Matrix.mulVec_add]

def x8E (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) (i : Fin d) : Module.End ℂ S :=
  rho.action (CliffordAlgebra.ι (x8Q d) (Pi.single i 1))

theorem x8E_sq (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) (i : Fin d) :
    x8E rho i * x8E rho i = -1 := by
  unfold x8E
  rw [← map_mul, CliffordAlgebra.ι_sq_scalar, x8_Q_single]; simp

theorem x8E_anti (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) (i j : Fin d) (h : i ≠ j) :
    x8E rho i * x8E rho j = -(x8E rho j * x8E rho i) := by
  unfold x8E
  rw [← map_mul rho.action, ← map_mul rho.action, ← map_neg rho.action]
  congr 1
  exact eq_neg_of_add_eq_zero_left (by rw [CliffordAlgebra.ι_mul_ι_add_swap, x8_polar_single i j h]; simp)

theorem x8_vec (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) (m : Fin d → ℂ) :
    rho.action (CliffordAlgebra.ι (x8Q d) m) = ∑ i, m i • x8E rho i := by
  have hm : m = ∑ i, m i • (Pi.single i 1 : Fin d → ℂ) := by
    ext k; simp [Pi.single_apply]
  conv_lhs => rw [hm]
  simp only [map_sum, map_smul, x8E]

theorem x8_commute_all (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) (A : Module.End ℂ S)
    (h : ∀ i, A * x8E rho i = x8E rho i * A) (x : CliffordAlgebra (x8Q d)) :
    A * rho.action x = rho.action x * A := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact (Algebra.commutes r A).symm
  | ι m =>
    rw [x8_vec, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_smul_comm, smul_mul_assoc, h]
  | mul a b ha hb => rw [map_mul, ← mul_assoc, ha, mul_assoc, hb, mul_assoc]
  | add a b ha hb => rw [map_add, mul_add, add_mul, ha, hb]

theorem x8_schur [FiniteDimensional ℂ S] (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S)
    (A : Module.End ℂ S) (h : ∀ i, A * x8E rho i = x8E rho i * A) :
    ∃ c : ℂ, A = algebraMap ℂ _ c := by
  haveI : Nontrivial S := rho.irreducible.1
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A
  refine ⟨c, ?_⟩
  have hst : SpinStable (Set.range rho.action) (Module.End.eigenspace A c) := by
    rintro B ⟨x, rfl⟩ v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have := congrArg (fun F => F v) (x8_commute_all rho A h x)
    simp only [Module.End.mul_apply] at this
    rw [this, hv, map_smul]
  rcases rho.irreducible.2 _ hst with h0 | h1
  · exact absurd h0 hc
  · ext v
    have hv : v ∈ Module.End.eigenspace A c := h1 ▸ Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hv
    simp [hv, Module.algebraMap_end_apply]

theorem x8_split {R : Type*} [Ring R] (e0 ei A : R) (h00 : e0 * e0 = -1)
    (hA1 : A * (e0 * ei) = (e0 * ei) * A) (hA2 : A * (ei * e0) = (ei * e0) * A) :
    (A - e0 * A * e0) * ei = ei * (A - e0 * A * e0) ∧
    (A + e0 * A * e0) * ei = -(ei * (A + e0 * A * e0)) := by
  have k1 : e0 * A * e0 * ei = -(ei * A) := by
    calc e0 * A * e0 * ei = e0 * (A * (e0 * ei)) := by simp only [mul_assoc]
      _ = e0 * ((e0 * ei) * A) := by rw [hA1]
      _ = (e0 * e0) * ei * A := by simp only [mul_assoc]
      _ = -(ei * A) := by rw [h00]; simp [mul_assoc]
  have k2 : ei * e0 * A * e0 = -(A * ei) := by
    calc ei * e0 * A * e0 = ((ei * e0) * A) * e0 := by simp only [mul_assoc]
      _ = (A * (ei * e0)) * e0 := by rw [hA2]
      _ = A * ei * (e0 * e0) := by simp only [mul_assoc]
      _ = -(A * ei) := by rw [h00]; simp
  constructor
  · rw [sub_mul, mul_sub, k1, ← mul_assoc ei, ← mul_assoc ei, k2]; abel
  · rw [add_mul, mul_add, k1, ← mul_assoc ei, ← mul_assoc ei, k2]; abel

def x8ω (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) : ℕ → Module.End ℂ S
  | 0 => 1
  | k + 1 => x8ω rho k * (if h : k < d then x8E rho ⟨k, h⟩ else 1)

theorem x8E_ω (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) (i : Fin d) :
    ∀ k, k ≤ d → x8E rho i * x8ω rho k =
      ((-1 : ℂ) ^ (k + if i.val < k then 1 else 0)) • (x8ω rho k * x8E rho i) := by
  intro k
  induction k with
  | zero => intro _; simp [x8ω]
  | succ k ih =>
    intro hk
    have hkd : k < d := hk
    have ih' := ih hkd.le
    simp only [x8ω, dif_pos hkd]
    rw [← mul_assoc, ih', smul_mul_assoc, mul_assoc, mul_assoc]
    by_cases hik : i = ⟨k, hkd⟩
    · subst hik
      simp only [lt_self_iff_false, if_false, add_zero, Nat.lt_succ_self, if_true]
      rw [pow_succ, pow_succ]; simp
    · have hne : i.val ≠ k := fun h => hik (Fin.ext h)
      rw [x8E_anti rho i ⟨k, hkd⟩ hik]
      have : (if i.val < k + 1 then 1 else 0) = (if i.val < k then 1 else 0) := by
        by_cases h : i.val < k
        · simp [h, Nat.lt_succ_of_lt h]
        · have : ¬ i.val < k + 1 := by omega
          simp [h, this]
      rw [this, mul_neg, smul_neg, ← neg_smul]
      congr 1
      rw [show k + 1 + (if i.val < k then 1 else 0) = (k + (if i.val < k then 1 else 0)) + 1 by ring,
        pow_succ]; ring

theorem x8N_ω (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) (N : Module.End ℂ S)
    (hN : ∀ i, N * x8E rho i = -(x8E rho i * N)) :
    ∀ k, k ≤ d → N * x8ω rho k = ((-1 : ℂ) ^ k) • (x8ω rho k * N) := by
  intro k
  induction k with
  | zero => intro _; simp [x8ω]
  | succ k ih =>
    intro hk
    have hkd : k < d := hk
    simp only [x8ω, dif_pos hkd]
    rw [← mul_assoc, ih hkd.le, smul_mul_assoc, mul_assoc, hN, mul_neg, smul_neg, ← neg_smul,
      ← mul_assoc, pow_succ]
    simp

theorem x8E_unit (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) (i : Fin d) :
    IsUnit (x8E rho i) :=
  ⟨⟨x8E rho i, -x8E rho i, by rw [mul_neg, x8E_sq, neg_neg], by rw [neg_mul, x8E_sq, neg_neg]⟩, rfl⟩

theorem x8ω_unit (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) : ∀ k, IsUnit (x8ω rho k)
  | 0 => isUnit_one
  | k + 1 => by
    simp only [x8ω]
    split_ifs
    · exact (x8ω_unit rho k).mul (x8E_unit rho _)
    · simpa using x8ω_unit rho k

theorem x8_mem_pair (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) (A : Module.End ℂ S)
    (hA : A ∈ schurAlgebra rho) (i j : Fin d) :
    A * (x8E rho i * x8E rho j) = (x8E rho i * x8E rho j) * A := by
  rw [schurAlgebra, Subalgebra.mem_centralizer_iff] at hA
  have hmem : x8E rho i * x8E rho j ∈ evenOperators rho :=
    ⟨⟨CliffordAlgebra.ι (x8Q d) (Pi.single i 1) * CliffordAlgebra.ι (x8Q d) (Pi.single j 1),
      CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero _ _ _⟩, by simp [x8E]⟩
  exact (hA _ hmem).symm

theorem x8_anti_vec (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) (Ω : Module.End ℂ S)
    (h : ∀ i, Ω * x8E rho i = -(x8E rho i * Ω)) (m : Fin d → ℂ) :
    Ω * rho.action (CliffordAlgebra.ι (x8Q d) m) = -(rho.action (CliffordAlgebra.ι (x8Q d) m) * Ω) := by
  rw [x8_vec, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_smul_comm, smul_mul_assoc, h, smul_neg]

theorem x8_mem_of_anti (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) (Ω : Module.End ℂ S)
    (h : ∀ i, Ω * x8E rho i = -(x8E rho i * Ω)) : Ω ∈ schurAlgebra rho := by
  rw [schurAlgebra, Subalgebra.mem_centralizer_iff]
  rintro g ⟨⟨a, ha⟩, rfl⟩
  show rho.action a * Ω = Ω * rho.action a
  induction a, ha using CliffordAlgebra.even_induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commutes r Ω
  | add x y hx hy ihx ihy => rw [map_add, add_mul, mul_add, ihx, ihy]
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    have h1 := x8_anti_vec rho Ω h m₁
    have h2 := x8_anti_vec rho Ω h m₂
    set a1 := rho.action (CliffordAlgebra.ι (x8Q d) m₁)
    set a2 := rho.action (CliffordAlgebra.ι (x8Q d) m₂)
    have h2' : a2 * Ω = -(Ω * a2) := by rw [h2, neg_neg]
    have h1' : a1 * Ω = -(Ω * a1) := by rw [h1, neg_neg]
    show rho.action (CliffordAlgebra.ι (x8Q d) m₁ * CliffordAlgebra.ι (x8Q d) m₂ * x) * Ω =
      Ω * rho.action (CliffordAlgebra.ι (x8Q d) m₁ * CliffordAlgebra.ι (x8Q d) m₂ * x)
    rw [map_mul, map_mul]
    calc a1 * a2 * rho.action x * Ω = a1 * (a2 * (rho.action x * Ω)) := by simp only [mul_assoc]
      _ = a1 * (a2 * (Ω * rho.action x)) := by rw [ih]
      _ = a1 * ((a2 * Ω) * rho.action x) := by simp only [mul_assoc]
      _ = -((a1 * Ω) * a2 * rho.action x) := by rw [h2']; simp [mul_assoc]
      _ = Ω * (a1 * a2 * rho.action x) := by rw [h1']; simp [mul_assoc]
      _ = Ω * a1 * a2 * rho.action x := by simp only [mul_assoc]

theorem x8_nontriv (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) : Nontrivial (Module.End ℂ S) := by
  haveI : Nontrivial S := rho.irreducible.1
  infer_instance

theorem x8_scalar_ne (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) (X : Module.End ℂ S)
    (hX : IsUnit X) (c : ℂ) (hc : X = algebraMap ℂ _ c) : c ≠ 0 := by
  haveI := x8_nontriv rho
  rintro rfl
  rw [hc, map_zero] at hX
  exact not_isUnit_zero hX

/-- decomposition of a Schur element into a scalar and an anticommuting part -/
theorem x8_decomp [FiniteDimensional ℂ S] (hd : 0 < d)
    (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) (A : Module.End ℂ S)
    (hA : A ∈ schurAlgebra rho) :
    ∃ p : ℂ, ∃ N : Module.End ℂ S, A = (1 / 2 : ℂ) • (algebraMap ℂ _ p + N) ∧
      ∀ i, N * x8E rho i = -(x8E rho i * N) := by
  set e0 := x8E rho ⟨0, hd⟩
  have hs := fun i => x8_split e0 (x8E rho i) A (x8E_sq rho _) (x8_mem_pair rho A hA _ _)
    (x8_mem_pair rho A hA _ _)
  obtain ⟨p, hp⟩ := x8_schur rho (A - e0 * A * e0) fun i => (hs i).1
  refine ⟨p, A + e0 * A * e0, ?_, fun i => (hs i).2⟩
  rw [← hp, smul_add, smul_sub]
  module

theorem x8_alg_mul (c : ℂ) (X : Module.End ℂ S) : algebraMap ℂ (Module.End ℂ S) c * X = c • X := by
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem x8_mul_alg (c : ℂ) (X : Module.End ℂ S) : X * algebraMap ℂ (Module.End ℂ S) c = c • X := by
  rw [← Algebra.commutes, x8_alg_mul]

theorem x8_ωE (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) (i : Fin d) :
    x8E rho i * x8ω rho d = ((-1 : ℂ) ^ (d + 1)) • (x8ω rho d * x8E rho i) := by
  rw [x8E_ω rho i d le_rfl, if_pos i.isLt]

theorem x8_odd [FiniteDimensional ℂ S] (hd : 0 < d) (hodd : ¬ Even d)
    (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) : schurAlgebra rho = ⊥ := by
  have hodd' : Odd d := Nat.not_even_iff_odd.1 hodd
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨p, N, hAN, hN⟩ := x8_decomp hd rho A hA
  obtain ⟨c, hc⟩ := x8_schur rho (x8ω rho d) fun i => by
    rw [x8_ωE, Even.neg_one_pow (by simpa [Nat.even_add_one] using hodd), one_smul]
  have hc0 := x8_scalar_ne rho _ (x8ω_unit rho d) c hc
  have h1 := x8N_ω rho N hN d le_rfl
  rw [Odd.neg_one_pow hodd', neg_one_smul, hc, x8_mul_alg, x8_alg_mul] at h1
  have hN0 : N = 0 := by
    have : (2 * c) • N = 0 := by rw [two_mul, add_smul]; nth_rewrite 1 [h1]; simp
    rcases smul_eq_zero.1 this with h | h
    · exact absurd h (mul_ne_zero two_ne_zero hc0)
    · exact h
  rw [hAN, hN0, add_zero, Algebra.mem_bot]
  exact ⟨(1 / 2 : ℂ) * p, by rw [map_mul, x8_alg_mul]⟩

/-- the even-dimensional structure: an anticommuting involution `u` in the Schur algebra
spanning it together with `1` -/
theorem x8_even_u [FiniteDimensional ℂ S] (hd : 0 < d) (hev : Even d)
    (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) :
    ∃ u : Module.End ℂ S, u ∈ schurAlgebra rho ∧ u * u = 1 ∧
      (∀ c : ℂ, u ≠ algebraMap ℂ _ c) ∧
      ∀ A ∈ schurAlgebra rho, ∃ α β : ℂ, A = algebraMap ℂ _ α + β • u := by
  haveI := x8_nontriv rho
  set ω := x8ω rho d
  have hanti : ∀ i, ω * x8E rho i = -(x8E rho i * ω) := fun i => by
    rw [x8_ωE, Odd.neg_one_pow (by simpa [Nat.odd_add_one] using hev), neg_one_smul, neg_neg]
  obtain ⟨s, hs⟩ := x8_schur rho (ω * ω) fun i => by
    rw [mul_assoc, hanti, mul_neg, ← mul_assoc, hanti, neg_mul, neg_neg, mul_assoc]
  have hs0 := x8_scalar_ne rho _ ((x8ω_unit rho d).mul (x8ω_unit rho d)) s hs
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq s (by norm_num : 0 < 2)
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact hs0 hr.symm
  set u := r⁻¹ • ω with hu
  have huanti : ∀ i, u * x8E rho i = -(x8E rho i * u) := fun i => by
    rw [hu, smul_mul_assoc, hanti, mul_smul_comm, smul_neg]
  have huu : u * u = 1 := by
    rw [hu, smul_mul_smul_comm, hs, Algebra.algebraMap_eq_smul_one, smul_smul, ← hr]
    field_simp
    simp
  refine ⟨u, x8_mem_of_anti rho u huanti, huu, ?_, ?_⟩
  · intro c hc
    have e0 := huanti ⟨0, hd⟩
    rw [hc, x8_alg_mul, x8_mul_alg] at e0
    have h2 : (2 * c) • x8E rho ⟨0, hd⟩ = 0 := by rw [two_mul, add_smul]; nth_rewrite 1 [e0]; simp
    have hE : x8E rho ⟨0, hd⟩ ≠ 0 := fun h => by
      have := x8E_sq rho ⟨0, hd⟩; rw [h, zero_mul] at this
      exact one_ne_zero (neg_eq_zero.1 this.symm)
    rcases smul_eq_zero.1 h2 with h | h
    · have hc0 : c = 0 := by simpa using h
      rw [hc, hc0, map_zero, zero_mul] at huu
      exact zero_ne_one huu
    · exact hE h
  · intro A hA
    obtain ⟨p, N, hAN, hN⟩ := x8_decomp hd rho A hA
    obtain ⟨b, hb⟩ := x8_schur rho (N * ω) fun i => by
      rw [mul_assoc, hanti, mul_neg, ← mul_assoc, hN, neg_mul, neg_neg, mul_assoc]
    have hNs : s • N = b • ω := by
      rw [← x8_mul_alg, ← hs, ← mul_assoc, hb, x8_alg_mul]
    have hN' : N = (s⁻¹ * b * r) • u := by
      rw [hu, smul_smul, mul_assoc, mul_assoc, mul_inv_cancel₀ hr0, mul_one, ← smul_smul, ← hNs,
        smul_smul, inv_mul_cancel₀ hs0, one_smul]
    refine ⟨(1 / 2 : ℂ) * p, (1 / 2 : ℂ) * (s⁻¹ * b * r), ?_⟩
    rw [hAN, hN', smul_add, map_mul, x8_alg_mul, smul_smul]

theorem x8_even_equiv [FiniteDimensional ℂ S] (hd : 0 < d) (hev : Even d)
    (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) :
    Nonempty (schurAlgebra rho ≃ₐ[ℂ] (ℂ × ℂ)) := by
  obtain ⟨u, hu, huu, hnot, hspan⟩ := x8_even_u hd hev rho
  set e : Module.End ℂ S := (1 / 2 : ℂ) • (1 + u) with he
  set f : Module.End ℂ S := (1 / 2 : ℂ) • (1 - u) with hf
  have hee : e * e = e := by
    rw [he, smul_mul_smul_comm, add_mul, mul_add, mul_add, huu]; simp only [one_mul, mul_one]; module
  have hff : f * f = f := by
    rw [hf, smul_mul_smul_comm, sub_mul, mul_sub, mul_sub, huu]; simp only [one_mul, mul_one]; module
  have hef : e * f = 0 := by
    rw [he, hf, smul_mul_smul_comm, add_mul, mul_sub, mul_sub, huu]; simp only [one_mul, mul_one]; module
  have hfe : f * e = 0 := by
    rw [he, hf, smul_mul_smul_comm, sub_mul, mul_add, mul_add, huu]; simp only [one_mul, mul_one]; module
  have hsum : e + f = 1 := by rw [he, hf]; module
  have he0 : e ≠ 0 := by
    intro h
    apply hnot (-1)
    have : u = -1 := by
      have h2 : (2 : ℂ) • e = 1 + u := by rw [he, smul_smul]; norm_num
      rw [h, smul_zero] at h2
      exact (neg_eq_of_add_eq_zero_right h2.symm).symm
    rw [this, map_neg, map_one]
  have hf0 : f ≠ 0 := by
    intro h
    apply hnot 1
    have : u = 1 := by
      have h2 : (2 : ℂ) • f = 1 - u := by rw [hf, smul_smul]; norm_num
      rw [h, smul_zero] at h2
      exact (sub_eq_zero.1 h2.symm).symm
    rw [this, map_one]
  let L : ℂ × ℂ →ₗ[ℂ] Module.End ℂ S :=
    (LinearMap.fst ℂ ℂ ℂ).smulRight e + (LinearMap.snd ℂ ℂ ℂ).smulRight f
  have hL : ∀ z : ℂ × ℂ, L z = z.1 • e + z.2 • f := fun z => rfl
  let g : ℂ × ℂ →ₐ[ℂ] Module.End ℂ S := AlgHom.ofLinearMap L
    (by rw [hL]; simp [hsum])
    (fun x y => by
      rw [hL, hL, hL]
      simp only [Prod.fst_mul, Prod.snd_mul, add_mul, mul_add, smul_mul_smul_comm, hee, hff, hef, hfe,
        smul_zero, add_zero, zero_add])
  have hg : ∀ z, g z = z.1 • e + z.2 • f := fun z => rfl
  have hmem : ∀ z, g z ∈ schurAlgebra rho := fun z => by
    rw [hg, he, hf]
    exact Subalgebra.add_mem _ (Subalgebra.smul_mem _ (Subalgebra.smul_mem _
      (Subalgebra.add_mem _ (Subalgebra.one_mem _) hu) _) _)
      (Subalgebra.smul_mem _ (Subalgebra.smul_mem _
      (Subalgebra.sub_mem _ (Subalgebra.one_mem _) hu) _) _)
  let g' := g.codRestrict (schurAlgebra rho) hmem
  have hinj : Function.Injective g' := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    have hz' : z.1 • e + z.2 • f = 0 := by
      have := congrArg Subtype.val hz; simpa [g', hg] using this
    have h1 : z.1 • e = 0 := by
      have := congrArg (· * e) hz'; simpa [add_mul, smul_mul_assoc, hee, hfe] using this
    have h2 : z.2 • f = 0 := by
      have := congrArg (· * f) hz'; simpa [add_mul, smul_mul_assoc, hff, hef] using this
    have z1 : z.1 = 0 := (smul_eq_zero.1 h1).resolve_right he0
    have z2 : z.2 = 0 := (smul_eq_zero.1 h2).resolve_right hf0
    exact Prod.ext z1 z2
  have hsurj : Function.Surjective g' := by
    rintro ⟨A, hA⟩
    obtain ⟨α, β, rfl⟩ := hspan A hA
    refine ⟨(α + β, α - β), Subtype.ext ?_⟩
    show g (α + β, α - β) = algebraMap ℂ _ α + β • u
    rw [hg, he, hf, Algebra.algebraMap_eq_smul_one]
    module
  exact ⟨(AlgEquiv.ofBijective g' ⟨hinj, hsurj⟩).symm⟩

theorem x8_main (d : ℕ) (hd : 0 < d)
    (S : Type*) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
    (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) :
    if Even d then Nonempty (schurAlgebra rho ≃ₐ[ℂ] (ℂ × ℂ))
    else Nonempty (schurAlgebra rho ≃ₐ[ℂ] ℂ) := by
  split_ifs with hev
  · exact x8_even_equiv hd hev rho
  · haveI := x8_nontriv rho
    exact ⟨(Subalgebra.equivOfEq _ _ (x8_odd hd hev rho)).trans (Algebra.botEquiv ℂ _)⟩

end X8

end QAlgorithms.Papers.Independent.Gap48.P17

open QAlgorithms.Papers.Independent.Gap48.P17 in
theorem solution (d : ℕ) (hd : 0 < d)
    (S : Type*) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
    (rho : SpinRepresentation (1 : Matrix (Fin d) (Fin d) ℂ) S) :
    if Even d then Nonempty (schurAlgebra rho ≃ₐ[ℂ] (ℂ × ℂ))
    else Nonempty (schurAlgebra rho ≃ₐ[ℂ] ℂ) :=
  QAlgorithms.Papers.Independent.Gap48.P17.x8_main d hd S rho
