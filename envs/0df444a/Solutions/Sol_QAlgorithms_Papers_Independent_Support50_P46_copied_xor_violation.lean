-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P46.copied_xor_violation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:11:37.194186+00:00
-- url     : https://prove2.me/submissions/71c86f95-4ac9-477c-9d7f-436ac242d1e7

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P46

-- ===== P46A =====

open scoped BigOperators ComplexConjugate
open Matrix Polynomial QAlgorithms

namespace X4P46

lemma cfc_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (f (d i) : ℂ)) := by
  classical
  let S : Finset ℝ := Finset.univ.image d
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) hx
  have hD : IsSelfAdjoint (diagonal (fun i => (d i : ℂ))) := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, diagonal_conjTranspose]
    congr 1; funext i; simp
  have hspec : ∀ x ∈ spectrum ℝ (diagonal (fun i => (d i : ℂ))), x ∈ S := by
    intro x hx
    rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage, spectrum_diagonal] at hx
    obtain ⟨i, hi⟩ := hx
    have : d i = x := by simpa using hi
    simp [S, ← this]
  rw [cfc_congr (g := fun x => p.eval x) (fun x hx => (hp x (hspec x hx)).symm),
    cfc_polynomial p _ hD]
  have : aeval (diagonal (fun i => (d i : ℂ))) p = diagonal (aeval (fun i => (d i : ℂ)) p) :=
    (aeval_algHom_apply (diagonalAlgHom ℝ) (fun i => (d i : ℂ)) p)
  rw [this, aeval_pi_apply]
  congr 1; funext i
  have h := aeval_algebraMap_apply ℂ (d i) p
  simp only [Complex.coe_algebraMap] at h
  rw [h, coe_aeval_eq_eval, hp _ (by simp [S] : d i ∈ S)]

lemma vn_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) :
    vnEntropy (diagonal (fun i => (d i : ℂ))) = -∑ i, d i * Real.logb 2 (d i) := by
  rw [vnEntropy, cfc_diag, trace_diagonal]
  simp

end X4P46

-- ===== P46B =====

open scoped BigOperators ComplexConjugate
open Matrix QAlgorithms

namespace X4P46

/-- Double sums of a pure density over a relation that, on the support, is the diagonal. -/
lemma core {X T : Type*} [Fintype X] [Fintype T] (e : T → X) (he : Function.Injective e)
    (c : ℂ) (ψ : X → ℂ) (h0 : ∀ x ∉ Set.range e, ψ x = 0) (h1 : ∀ t, ψ (e t) = c)
    (P : X → X → Prop) {_ : ∀ x y, Decidable (P x y)} (Q : T → Prop) [DecidablePred Q]
    (hP : ∀ t t', P (e t) (e t') ↔ t = t' ∧ Q t) :
    ∑ x, ∑ y, (if P x y then ψ x * conj (ψ y) else 0) =
      ∑ t, if Q t then c * conj c else 0 := by
  classical
  symm
  refine Fintype.sum_of_injective e he _ _ ?_ ?_
  · intro x hx; simp [h0 x hx]
  intro t
  symm
  rw [← Fintype.sum_of_injective e he (fun t' => if P (e t) (e t') then ψ (e t) * conj (ψ (e t'))
    else 0) _ (fun y hy => by simp [h0 y hy]) (fun _ => rfl)]
  rw [Finset.sum_eq_single t]
  · have := hP t t; by_cases hq : Q t <;> simp_all
  · intro t' _ ht'; have := hP t t'; simp_all [Ne.symm ht']
  · simp

lemma marg {X T K F : Type*} [Fintype X] [Fintype T] [Fintype K] [DecidableEq K]
    (e : T → X) (he : Function.Injective e)
    (ψ : EuclideanSpace ℂ X) (h0 : ∀ x ∉ Set.range e, ψ x = 0) (h1 : ∀ t, ψ (e t) = (1/2 : ℂ))
    (keep : X → K) (forget : X → F) (hf : ∀ t t', forget (e t) = forget (e t') → t = t') :
    QAlgorithms.Papers.Independent.Gap48.P20.redistributionMarginal (pureDensity ψ) keep forget =
      diagonal (fun a => ((∑ t, if keep (e t) = a then (1/4 : ℝ) else 0 : ℝ) : ℂ)) := by
  classical
  ext a b
  unfold QAlgorithms.Papers.Independent.Gap48.P20.redistributionMarginal pureDensity
  simp only [Matrix.of_apply]
  refine (core e he (1/2) _ h0 h1 _ (fun t => keep (e t) = a ∧ keep (e t) = b) ?_).trans ?_
  rotate_left
  · by_cases hab : a = b
    · subst hab; simp only [diagonal_apply_eq, and_self]; push_cast
      refine Finset.sum_congr rfl fun t _ => ?_
      split_ifs <;> simp [Complex.ext_iff]; norm_num
    · rw [diagonal_apply_ne _ hab]
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [if_neg]; rintro ⟨h1, h2⟩; exact hab (h1.symm.trans h2)
  · intro t t'
    constructor
    · rintro ⟨h1, h2, h3⟩; obtain rfl := hf t t' h3; exact ⟨rfl, h1, h2⟩
    · rintro ⟨rfl, h1, h2⟩; exact ⟨h1, h2, rfl⟩

lemma vn_diag' {ι : Type*} [Fintype ι] {i1 i2 : DecidableEq ι} (d : ι → ℝ) :
    @vnEntropy ι _ i1 (@diagonal _ _ i2 _ (fun i => (d i : ℂ))) = -∑ i, d i * Real.logb 2 (d i) := by
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  exact vn_diag d

lemma ent_eval {T K : Type*} [Fintype T] [Fintype K] [DecidableEq K] (g : T → K) (q : ℝ) :
    -∑ a, (∑ t, if g t = a then q else 0) * Real.logb 2 (∑ t, if g t = a then q else 0) =
      -∑ t, q * Real.logb 2 (q * (Finset.univ.filter (fun t' => g t' = g t)).card) := by
  congr 1
  have hw : ∀ a, (∑ t, if g t = a then q else 0) = q * (Finset.univ.filter (fun t' => g t' = a)).card := by
    intro a; rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  simp_rw [hw]
  have : ∀ a, q * ((Finset.univ.filter (fun t' => g t' = a)).card : ℝ) *
      Real.logb 2 (q * (Finset.univ.filter (fun t' => g t' = a)).card) =
      ∑ t, if g t = a then q * Real.logb 2 (q * (Finset.univ.filter (fun t' => g t' = g t)).card)
        else 0 := by
    intro a
    rw [← Finset.sum_filter, Finset.sum_congr rfl (g := fun _ => q * Real.logb 2
      (q * (Finset.univ.filter (fun t' => g t' = a)).card))]
    · rw [Finset.sum_const, nsmul_eq_mul]; ring
    · intro t ht; rw [(Finset.mem_filter.mp ht).2]
  simp_rw [this]
  rw [Finset.sum_comm]
  simp

end X4P46

-- ===== P46C =====

open scoped BigOperators ComplexConjugate
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Support50.P46

namespace X4P46

def emb (t : Bool × Bool) : Qubits 6 := ![t.1, t.1, t.2, t.2, xor t.1 t.2, xor t.1 t.2]

lemma emb_inj : Function.Injective emb := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h0 := congrFun h 0; have h2 := congrFun h 2
  simp [emb] at h0 h2; simp [h0, h2]

lemma h0 : ∀ x ∉ Set.range emb, copiedSixVector x = 0 := by
  intro x hx
  simp only [copiedSixVector]
  rw [if_neg]
  rintro ⟨h01, h23, h45, h4⟩
  apply hx
  refine ⟨(x 0, x 2), funext fun i => ?_⟩
  fin_cases i <;> simp [emb, ← h01, ← h23, ← h45, h4]

lemma h1 : ∀ t, copiedSixVector (emb t) = (1/2 : ℂ) := by
  rintro ⟨a, b⟩
  simp [copiedSixVector, emb]

lemma ent (s : Finset (Fin 6))
    (hf : ∀ t t', (fun i : {i // i ∉ s} => emb t i.val) = (fun i => emb t' i.val) → t = t') :
    Papers.Independent.Gap48.P20.subsystemEntropy copiedSixDensity
      (fun x => fun i : {i // i ∈ s} => x i.val) (fun x => fun i : {i // i ∉ s} => x i.val) =
      -∑ t, (1/4 : ℝ) * Real.logb 2 ((1/4 : ℝ) * (Finset.univ.filter
        (fun t' => (fun i : {i // i ∈ s} => emb t' i.val) = (fun i => emb t i.val))).card) := by
  unfold Papers.Independent.Gap48.P20.subsystemEntropy copiedSixDensity
  rw [marg emb emb_inj _ h0 h1 _ _ hf, vn_diag', ent_eval]

lemma val (cnt : Bool × Bool → ℕ) (n : ℕ) (hc : ∀ t, cnt t = n) :
    -∑ t, (1/4 : ℝ) * Real.logb 2 ((1/4 : ℝ) * (cnt t : ℝ)) = -Real.logb 2 (n / 4) := by
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool]
  simp; ring_nf

lemma lb4 : Real.logb 2 ((1 : ℕ) / 4 : ℝ) = -2 := by
  rw [show ((1 : ℕ) / 4 : ℝ) = 2 ^ (-2 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]

lemma lb2 : Real.logb 2 ((2 : ℕ) / 4 : ℝ) = -1 := by
  rw [show ((2 : ℕ) / 4 : ℝ) = 2 ^ (-1 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]

lemma i3 : tripartiteInformation copiedSixDensity {0} {1} {2, 4} = 1 := by
  simp only [tripartiteInformation]
  rw [ent {0} (by decide), ent {1} (by decide), ent {2, 4} (by decide), ent ({0} ∪ {1}) (by decide),
    ent ({1} ∪ {2, 4}) (by decide), ent ({0} ∪ {2, 4}) (by decide),
    ent ({0} ∪ {1} ∪ {2, 4}) (by decide)]
  rw [val _ 2 (by decide), val _ 2 (by decide), val _ 1 (by decide), val _ 2 (by decide),
    val _ 1 (by decide), val _ 1 (by decide), val _ 1 (by decide)]
  rw [lb4, lb2]; norm_num

end X4P46

-- ===== P46D =====

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Support50.P46

namespace X4P46

lemma state : IsState copiedSixVector := by
  rw [IsState, EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  rw [← Fintype.sum_of_injective emb emb_inj (fun t => ‖copiedSixVector (emb t)‖ ^ 2) _
    (fun x hx => by simp [h0 x hx]) (fun _ => rfl)]
  simp only [h1]; simp; norm_num

lemma dens : IsDensityMatrix copiedSixDensity := by
  refine ⟨?_, ?_⟩
  · have : copiedSixDensity = vecMulVec (fun x => copiedSixVector x) (star fun x => copiedSixVector x) := by
      ext x y; simp [copiedSixDensity, pureDensity, vecMulVec]
    rw [this]; exact posSemidef_vecMulVec_self_star _
  · rw [Matrix.trace]
    simp only [copiedSixDensity, pureDensity, Matrix.diag, Matrix.of_apply]
    rw [← Fintype.sum_of_injective emb emb_inj (fun t => copiedSixVector (emb t) * conj (copiedSixVector (emb t))) _
      (fun x hx => by simp [h0 x hx]) (fun _ => rfl)]
    simp only [h1, map_div₀, map_one, map_ofNat]; norm_num

lemma cnt3 : ∀ u v : Qubits 3, (Finset.univ.filter (fun t : Bool × Bool =>
    (∀ j : Fin 3, emb t (![0, 2, 4] j) = u j) ∧ (∀ j : Fin 3, emb t (![0, 2, 4] j) = v j))).card =
    if u = v ∧ u 2 = xor (u 0) (u 1) then 1 else 0 := by decide

lemma three : threeMarginal copiedSixDensity ![0, 2, 4] = xorClassical := by
  ext u v
  unfold threeMarginal copiedSixDensity pureDensity
  simp only [Matrix.of_apply]
  refine (core emb emb_inj (1/2) _ h0 h1 _ (fun t => (∀ j : Fin 3, emb t (![0, 2, 4] j) = u j) ∧
    (∀ j : Fin 3, emb t (![0, 2, 4] j) = v j)) ?_).trans ?_
  · rintro ⟨a, b⟩ ⟨c, d⟩
    constructor
    · rintro ⟨hu, hv, hr⟩
      have e1 := hr 1 (by decide); have e3 := hr 3 (by decide)
      simp [emb] at e1 e3; subst e1; subst e3; exact ⟨rfl, hu, hv⟩
    · rintro ⟨h, hu, hv⟩; cases h; exact ⟨hu, hv, fun _ _ => rfl⟩
  · rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, cnt3]
    unfold xorClassical
    split_ifs <;> simp_all [map_ofNat]; norm_num

end X4P46


-- ===== P46Sol1 =====

noncomputable section

open scoped BigOperators ComplexConjugate

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P46

open QAlgorithms.Papers.Independent.Gap48.P20 (subsystemEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

theorem solution :
    IsState copiedSixVector ∧ IsDensityMatrix copiedSixDensity ∧
    threeMarginal copiedSixDensity ![0, 2, 4] = xorClassical ∧
    tripartiteInformation copiedSixDensity {0} {1} {2, 4} = 1 := by
  refine ⟨X4P46.state, X4P46.dens, ?_, ?_⟩
  · convert X4P46.three
  · convert X4P46.i3

end
