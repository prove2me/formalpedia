-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P46.classical_examples
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:24:32.50798+00:00
-- url     : https://prove2.me/submissions/e0ecf795-4459-4bee-a439-3e98b36b64c1

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

-- ===== P46H =====

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Support50.P46

namespace X4P46

lemma margC {X T K F : Type*} [Fintype X] [Fintype T] [Fintype K] [DecidableEq K]
    (e : T → X) (he : Function.Injective e) (q : ℝ) (ρ : Matrix X X ℂ)
    (hoff : ∀ x y, x ≠ y → ρ x y = 0) (hd0 : ∀ x ∉ Set.range e, ρ x x = 0)
    (hd1 : ∀ t, ρ (e t) (e t) = q) (keep : X → K) (forget : X → F) :
    QAlgorithms.Papers.Independent.Gap48.P20.redistributionMarginal ρ keep forget =
      diagonal (fun a => ((∑ t, if keep (e t) = a then q else 0 : ℝ) : ℂ)) := by
  classical
  ext a b
  unfold QAlgorithms.Papers.Independent.Gap48.P20.redistributionMarginal
  refine (Finset.sum_congr rfl fun x _ => ?_).trans
    (?_ : (∑ x, if keep x = a ∧ keep x = b then ρ x x else 0) = _)
  · rw [Finset.sum_eq_single x]
    · split_ifs <;> tauto
    · intro y _ hy; split_ifs <;> simp [hoff x y (Ne.symm hy)]
    · simp
  rw [← Fintype.sum_of_injective e he (fun t => if keep (e t) = a ∧ keep (e t) = b then ρ (e t) (e t) else 0)
    _ (fun x hx => by simp [hd0 x hx]) (fun _ => rfl)]
  simp only [hd1]
  by_cases hab : a = b
  · subst hab; simp only [and_self, diagonal_apply_eq]; push_cast
    exact Finset.sum_congr rfl fun t _ => by split_ifs <;> simp
  · rw [diagonal_apply_ne _ hab]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]; rintro ⟨h1, h2⟩; exact hab (h1.symm.trans h2)

lemma entC {X T : Type*} [Fintype X] [Fintype T] (s : Finset X) [DecidableEq X]
    (e : T → (X → Bool)) (he : Function.Injective e) (q : ℝ) (ρ : Matrix (X → Bool) (X → Bool) ℂ)
    (hoff : ∀ x y, x ≠ y → ρ x y = 0) (hd0 : ∀ x ∉ Set.range e, ρ x x = 0)
    (hd1 : ∀ t, ρ (e t) (e t) = q) :
    QAlgorithms.Papers.Independent.Gap48.P20.subsystemEntropy ρ
      (fun x => fun i : {i // i ∈ s} => x i.val) (fun x => fun i : {i // i ∉ s} => x i.val) =
      -∑ t, q * Real.logb 2 (q * (Finset.univ.filter
        (fun t' => (fun i : {i // i ∈ s} => e t' i.val) = (fun i => e t i.val))).card) := by
  unfold QAlgorithms.Papers.Independent.Gap48.P20.subsystemEntropy
  rw [margC e he q ρ hoff hd0 hd1, vn_diag', ent_eval]

def eR (b : Bool) : Qubits 3 := ![b, b, b]
def eX (t : Bool × Bool) : Qubits 3 := ![t.1, t.2, xor t.1 t.2]

lemma eR_inj : Function.Injective eR := by
  intro a b h; have := congrFun h 0; simpa [eR] using this
lemma eX_inj : Function.Injective eX := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h0 := congrFun h 0; have h1 := congrFun h 1
  simp [eX] at h0 h1; simp [h0, h1]

lemma R0 : ∀ x y, x ≠ y → redundantClassical x y = 0 := by
  intro x y h; simp [redundantClassical, h]
lemma R1 : ∀ x ∉ Set.range eR, redundantClassical x x = 0 := by
  intro x hx; simp only [redundantClassical]; rw [if_neg]
  rintro ⟨-, h01, h12⟩; apply hx
  refine ⟨x 0, funext fun i => ?_⟩; fin_cases i <;> simp [eR, h01, h12]
lemma R2 : ∀ t, redundantClassical (eR t) (eR t) = ((1/2 : ℝ) : ℂ) := by
  intro t; simp [redundantClassical, eR]
lemma X0 : ∀ x y, x ≠ y → xorClassical x y = 0 := by
  intro x y h; simp [xorClassical, h]
lemma X1 : ∀ x ∉ Set.range eX, xorClassical x x = 0 := by
  intro x hx; simp only [xorClassical]; rw [if_neg]
  rintro ⟨-, h2⟩; apply hx
  refine ⟨(x 0, x 1), funext fun i => ?_⟩; fin_cases i <;> simp [eX, h2]
lemma X2 : ∀ t, xorClassical (eX t) (eX t) = ((1/4 : ℝ) : ℂ) := by
  rintro ⟨a, b⟩; simp [xorClassical, eX]

lemma valq {T : Type*} [Fintype T] (q : ℝ) (cnt : T → ℕ) (n : ℕ) (hc : ∀ t, cnt t = n) :
    -∑ t, q * Real.logb 2 (q * (cnt t : ℝ)) = -(Fintype.card T * q) * Real.logb 2 (q * n) := by
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

lemma lg2 : Real.logb 2 ((1/2 : ℝ) * ((1 : ℕ) : ℝ)) = -1 := by
  rw [show (1/2 : ℝ) * ((1 : ℕ) : ℝ) = 2 ^ (-1 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
lemma lg4 : Real.logb 2 ((1/4 : ℝ) * ((1 : ℕ) : ℝ)) = -2 := by
  rw [show (1/4 : ℝ) * ((1 : ℕ) : ℝ) = 2 ^ (-2 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
lemma lg42 : Real.logb 2 ((1/4 : ℝ) * ((2 : ℕ) : ℝ)) = -1 := by
  rw [show (1/4 : ℝ) * ((2 : ℕ) : ℝ) = 2 ^ (-1 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]

lemma iR : tripartiteInformation redundantClassical {0} {1} {2} = 1 := by
  simp only [tripartiteInformation]
  simp only [entC _ eR eR_inj _ _ R0 R1 R2]
  rw [valq _ _ 1 (by decide), valq _ _ 1 (by decide), valq _ _ 1 (by decide), valq _ _ 1 (by decide),
    valq _ _ 1 (by decide), valq _ _ 1 (by decide), valq _ _ 1 (by decide)]
  simp only [lg2, Fintype.card_bool]; norm_num

lemma iX : tripartiteInformation xorClassical {0} {1} {2} = -1 := by
  simp only [tripartiteInformation]
  simp only [entC _ eX eX_inj _ _ X0 X1 X2]
  rw [valq _ _ 2 (by decide), valq _ _ 2 (by decide), valq _ _ 2 (by decide), valq _ _ 1 (by decide),
    valq _ _ 1 (by decide), valq _ _ 1 (by decide), valq _ _ 1 (by decide)]
  simp only [lg4, lg42, Fintype.card_prod, Fintype.card_bool]; norm_num

lemma densC {X T : Type*} [Fintype X] [DecidableEq X] [Fintype T] (e : T → X) (he : Function.Injective e)
    (q : ℝ) (hq : 0 ≤ q) (hsum : Fintype.card T * q = 1) (ρ : Matrix X X ℂ)
    (hoff : ∀ x y, x ≠ y → ρ x y = 0) (hd0 : ∀ x ∉ Set.range e, ρ x x = 0)
    (hd1 : ∀ t, ρ (e t) (e t) = q) : IsDensityMatrix ρ := by
  classical
  have hdiag : ρ = diagonal (fun x => ρ x x) := by
    ext x y; by_cases h : x = y
    · subst h; simp
    · simp [h, hoff x y h]
  refine ⟨?_, ?_⟩
  · rw [hdiag, posSemidef_diagonal_iff]
    intro x
    by_cases hx : x ∈ Set.range e
    · obtain ⟨t, rfl⟩ := hx; rw [hd1]; exact_mod_cast hq
    · rw [hd0 x hx]
  · rw [Matrix.trace]
    simp only [Matrix.diag]
    rw [← Fintype.sum_of_injective e he (fun t => ρ (e t) (e t)) _ (fun x hx => hd0 x hx) (fun _ => rfl)]
    simp only [hd1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact_mod_cast hsum

end X4P46

-- ===== P46Sol3 =====

noncomputable section

open scoped BigOperators ComplexConjugate

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P46

open QAlgorithms.Papers.Independent.Gap48.P20 (subsystemEntropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

theorem solution :
    IsDensityMatrix redundantClassical ∧ IsDensityMatrix xorClassical ∧
    tripartiteInformation redundantClassical {0} {1} {2} = 1 ∧
    tripartiteInformation xorClassical {0} {1} {2} = -1 := by
  refine ⟨X4P46.densC X4P46.eR X4P46.eR_inj (1/2) (by norm_num) (by norm_num) _
      X4P46.R0 X4P46.R1 X4P46.R2,
    X4P46.densC X4P46.eX X4P46.eX_inj (1/4) (by norm_num) (by norm_num) _
      X4P46.X0 X4P46.X1 X4P46.X2, ?_, ?_⟩
  · convert X4P46.iR
  · convert X4P46.iX

end
