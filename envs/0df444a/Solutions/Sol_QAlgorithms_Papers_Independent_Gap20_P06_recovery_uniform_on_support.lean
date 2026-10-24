-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P06.recovery_uniform_on_support
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:00:17.990208+00:00
-- url     : https://prove2.me/submissions/0a8ee1f6-b936-4f4d-b757-a4e9f527c747

import Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P06_coherentInformation_bound_and_equality
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P06


/-! X6: Schmidt-form helpers for Gap20.P06.schmidt_recovery_construction. -/

open scoped ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6SR
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Gap20.P06

lemma inner_eq {A : Type*} [Fintype A] (x y : EuclideanSpace ℂ A) :
    inner ℂ x y = ∑ a, conj (x a) * y a := by
  simp [PiLp.inner_apply, mul_comm]

lemma on_iff {ι A : Type*} [Fintype A] [DecidableEq ι] (v : ι → EuclideanSpace ℂ A) :
    Orthonormal ℂ v ↔ ∀ i j, ∑ a, conj (v i a) * v j a = if i = j then 1 else 0 := by
  rw [orthonormal_iff_ite]; simp only [inner_eq]

lemma spec_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hh : H.IsHermitian) :
    H = ∑ x, ((hh.eigenvalues x : ℝ) : ℂ) • pureDensity (hh.eigenvectorBasis x) := by
  have e : H = (hh.eigenvectorUnitary : Matrix ι ι ℂ) *
      diagonal (fun i => ((hh.eigenvalues i : ℝ) : ℂ)) * (hh.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
    conv_lhs => rw [hh.spectral_theorem]
    rfl
  conv_lhs => rw [e]
  ext a b
  simp only [mul_apply, diagonal_apply, conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
    pureDensity, of_apply, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Finset.sum_mul, IsHermitian.eigenvectorUnitary_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

lemma sum_split {ι M : Type*} [Fintype ι] [AddCommMonoid M] {n : ℕ} (p : ι → Prop) [DecidablePred p]
    (g : ι → M) (hg : ∀ x, ¬ p x → g x = 0) (e : {x // p x} ≃ Fin n) :
    ∑ x, g x = ∑ i : Fin n, g (e.symm i).1 := by
  rw [← Fintype.sum_subtype_add_sum_subtype p g,
    Finset.sum_eq_zero (s := (Finset.univ : Finset {x // ¬ p x})) (fun x _ => hg x.1 x.2), add_zero]
  exact (e.symm.sum_comp (fun x : {x // p x} => g x.1)).symm

lemma spec_pos {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.PosSemidef)
    (ht : H.trace = 1) :
    ∃ (k : ℕ) (c : Fin k → ℝ) (v : Fin k → EuclideanSpace ℂ ι), 0 < k ∧ (∀ i, 0 < c i) ∧
      ∑ i, c i = 1 ∧ Orthonormal ℂ v ∧ H = ∑ i, (c i : ℂ) • pureDensity (v i) := by
  set hh := hH.isHermitian
  set ev := hh.eigenvalues
  set S := {x : ι // 0 < ev x}
  set e := Fintype.equivFin S
  have hz : ∀ x, ¬ 0 < ev x → ev x = 0 :=
    fun x hx => le_antisymm (not_lt.1 hx) (hH.eigenvalues_nonneg x)
  have htot : ∑ x, ev x = 1 := by
    have := hh.trace_eq_sum_eigenvalues
    rw [ht] at this
    have h2 : ((∑ x, ev x : ℝ) : ℂ) = 1 := by push_cast; exact this.symm
    exact_mod_cast h2
  have hsum : ∑ i : Fin (Fintype.card S), ev (e.symm i).1 = 1 := by
    rw [← sum_split (fun x => 0 < ev x) ev hz e]; exact htot
  have hne : Nonempty S := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have : ∑ x, ev x = 0 := Finset.sum_eq_zero fun x _ => hz x fun h => hn.false ⟨x, h⟩
    rw [htot] at this; exact one_ne_zero this
  refine ⟨Fintype.card S, fun i => ev (e.symm i).1, fun i => hh.eigenvectorBasis (e.symm i).1,
    Fintype.card_pos, fun i => (e.symm i).2, hsum, ?_, ?_⟩
  · exact hh.eigenvectorBasis.orthonormal.comp _
      (Subtype.val_injective.comp e.symm.injective)
  · conv_lhs => rw [spec_sum hh]
    exact sum_split (fun x => 0 < ev x) _ (fun x h => by show ((ev x : ℝ) : ℂ) • _ = 0; rw [hz x h]; simp) e

lemma sq_inv (x : ℝ) (hx : 0 < x) :
    ((Real.sqrt x)⁻¹ : ℂ) * (x : ℂ) * ((Real.sqrt x)⁻¹ : ℂ) = 1 := by
  have h1 : (Real.sqrt x : ℂ) * (Real.sqrt x : ℂ) = x := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hx.le]
  have h2 : (Real.sqrt x : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hx).ne'
  rw [← h1]; field_simp

/-- a vector on `A × B` whose `A`-marginal is `Σ c_i v_i v_i*` (orthonormal `v`, `c > 0`)
has the Schmidt form `Σ √c_i v_i ⊗ w_i` with orthonormal `w`. -/
lemma purif {ι A B : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    (Ψ : EuclideanSpace ℂ (A × B)) (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (v : ι → EuclideanSpace ℂ A) (hv : Orthonormal ℂ v)
    (hω : ∀ a a', ∑ b, Ψ (a, b) * conj (Ψ (a', b)) = ∑ i, (c i : ℂ) * (v i a * conj (v i a'))) :
    ∃ w : ι → EuclideanSpace ℂ B, Orthonormal ℂ w ∧
      ∀ a b, Ψ (a, b) = ∑ i, (Real.sqrt (c i) : ℂ) * (v i a * w i b) := by
  set M : Matrix A B ℂ := of fun a b => Ψ (a, b)
  set V : Matrix A ι ℂ := of fun a i => v i a
  set C : Matrix ι ι ℂ := diagonal fun i => (c i : ℂ)
  set Si : Matrix ι ι ℂ := diagonal fun i => ((Real.sqrt (c i))⁻¹ : ℂ)
  set Sq : Matrix ι ι ℂ := diagonal fun i => (Real.sqrt (c i) : ℂ)
  have hVV : Vᴴ * V = 1 := by
    ext i j
    have := (on_iff v).1 hv i j
    simpa [V, mul_apply, one_apply] using this
  have hMM : M * Mᴴ = V * C * Vᴴ := by
    ext a a'
    simp only [M, V, C, mul_apply, conjTranspose_apply, of_apply, diagonal_apply, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, RCLike.star_def, hω]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  set P := V * Vᴴ
  have hPh : Pᴴ = P := by simp [P, conjTranspose_mul, Matrix.mul_assoc]
  have hPω : P * (M * Mᴴ) = M * Mᴴ := by
    rw [hMM]; simp only [P, Matrix.mul_assoc]; rw [← Matrix.mul_assoc Vᴴ V, hVV, Matrix.one_mul]
  have hωP : (M * Mᴴ) * P = M * Mᴴ := by
    rw [hMM]; simp only [P, Matrix.mul_assoc]; rw [← Matrix.mul_assoc Vᴴ V, hVV, Matrix.one_mul]
  have hD : (M - P * M) * (M - P * M)ᴴ = 0 := by
    rw [conjTranspose_sub, conjTranspose_mul, hPh, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      ← Matrix.mul_assoc M Mᴴ P, hωP, Matrix.mul_assoc P M Mᴴ, hPω, Matrix.mul_assoc P M,
      ← Matrix.mul_assoc M Mᴴ P, hωP, hPω, sub_self]
  have hPM : P * M = M := (sub_eq_zero.1 (self_mul_conjTranspose_eq_zero.1 hD)).symm
  set W : Matrix ι B ℂ := Si * Vᴴ * M
  have hSC : Si * C * Si = 1 := by
    simp only [Si, C, diagonal_mul_diagonal]
    rw [← diagonal_one]; congr 1; funext i; exact sq_inv _ (hc i)
  have hWW : W * Wᴴ = 1 := by
    have hSi : Siᴴ = Si := by
      rw [diagonal_conjTranspose]; congr 1; funext i
      simp [Si, ← Complex.ofReal_inv, Complex.conj_ofReal]
    calc W * Wᴴ = Si * (Vᴴ * (M * Mᴴ) * V) * Siᴴ := by
            simp only [W, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = 1 := by
            rw [hMM, hSi]
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc Vᴴ V, hVV, Matrix.one_mul, ← Matrix.mul_assoc Vᴴ V, hVV,
              Matrix.one_mul, ← Matrix.mul_assoc, hSC]
  have hrec : V * Sq * W = M := by
    have : Sq * Si = 1 := by
      simp only [Si, Sq, diagonal_mul_diagonal]
      rw [← diagonal_one]; congr 1; funext i
      have h2 : (Real.sqrt (c i) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (hc i)).ne'
      field_simp
    simp only [W, ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc V Sq Si, this, Matrix.mul_one]; exact hPM
  refine ⟨fun i => WithLp.toLp 2 (W i), ?_, ?_⟩
  · rw [on_iff]; intro i j
    have h1 : (W * Wᴴ) j i = ∑ b, conj (W i b) * W j b := by
      simp only [mul_apply, conjTranspose_apply, RCLike.star_def]
      exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    show ∑ b, conj (W i b) * W j b = _
    rw [← h1, hWW, one_apply]; by_cases h : i = j <;> simp [h, eq_comm]
  · intro a b
    have := congrFun (congrFun hrec a) b
    simp only [M, V, Sq, mul_apply, diagonal_apply, of_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [PiLp.toLp_apply]; ring

end X6SR


/-! X6: dilation and recovery computations for Gap20.P06.schmidt_recovery_construction. -/

open scoped ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6SR
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Gap20.P06

attribute [local instance] Classical.propDecidable Classical.decEq

lemma pd_trace {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    (pureDensity v).trace = 1 := by
  have h := EuclideanSpace.norm_sq_eq v
  rw [hv] at h
  simp only [Matrix.trace, Matrix.diag_apply, pureDensity, Matrix.of_apply, Complex.mul_conj]
  have : ∑ i, ((Complex.normSq (v i) : ℝ) : ℂ) = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [this, ← h]; simp

lemma mul3_entry {P Q : Type*} [Fintype Q] (X : Matrix P Q ℂ) (B : Matrix Q Q ℂ) (Y : Matrix P Q ℂ)
    (i j : P) : (X * B * Yᴴ) i j = ∑ x, ∑ x', X i x * B x x' * star (Y j x') := by
  simp only [mul_apply, conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

variable {R Q E : Type*} [Fintype R] [Fintype Q] [Fintype E]

/-- the `(r, r')` block of `ψψ*`. -/
def blk (psi : EuclideanSpace ℂ (R × Q)) (r r' : R) : Matrix Q Q ℂ :=
  of fun i i' => psi (r, i) * conj (psi (r', i'))

lemma phi_apply (U : Matrix.unitaryGroup (Q × E) ℂ) (eta : EuclideanSpace ℂ E)
    (psi : EuclideanSpace ℂ (R × Q)) (r : R) (x : Q × E) :
    dilatedVector U eta psi (r, x) =
      ∑ y : Q × E, (U : Matrix (Q × E) (Q × E) ℂ) x y * (psi (r, y.1) * eta y.2) := by
  show Matrix.mulVec ((1 : Matrix R R ℂ) ⊗ₖ (U : Matrix (Q × E) (Q × E) ℂ))
    (fun z : R × (Q × E) => psi (z.1, z.2.1) * eta z.2.2) (r, x) = _
  rw [mulVec, dotProduct, Fintype.sum_prod_type, Fintype.sum_eq_single r]
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [kroneckerMap_apply, one_apply_eq, one_mul]
  · intro r1 h
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [kroneckerMap_apply, one_apply_ne (Ne.symm h), zero_mul, zero_mul]

lemma G_apply (U : Matrix.unitaryGroup (Q × E) ℂ) (eta : EuclideanSpace ℂ E)
    (psi : EuclideanSpace ℂ (R × Q)) (r r' : R) (x y : Q × E) :
    ((U : Matrix (Q × E) (Q × E) ℂ) * Matrix.kronecker (blk psi r r') (pureDensity eta) *
      (U : Matrix (Q × E) (Q × E) ℂ)ᴴ) x y =
      dilatedVector U eta psi (r, x) * conj (dilatedVector U eta psi (r', y)) := by
  rw [mul3_entry, phi_apply, phi_apply, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => ?_
  simp only [Matrix.kronecker, kroneckerMap_apply, blk, pureDensity, of_apply, map_mul,
    RCLike.star_def]
  ring

lemma tr_G (U : Matrix.unitaryGroup (Q × E) ℂ) (eta : EuclideanSpace ℂ E)
    (heta : ‖eta‖ = 1) (psi : EuclideanSpace ℂ (R × Q)) (r r' : R) :
    ∑ x : Q × E, dilatedVector U eta psi (r, x) * conj (dilatedVector U eta psi (r', x)) =
      ∑ q, psi (r, q) * conj (psi (r', q)) := by
  have hU : (U : Matrix (Q × E) (Q × E) ℂ)ᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff'.1 U.2)
  have e1 : trace ((U : Matrix (Q × E) (Q × E) ℂ) * Matrix.kronecker (blk psi r r') (pureDensity eta) *
      (U : Matrix (Q × E) (Q × E) ℂ)ᴴ) = trace (blk psi r r') := by
    rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
    rw [show Matrix.kronecker (blk psi r r') (pureDensity eta) = blk psi r r' ⊗ₖ pureDensity eta
      from rfl, trace_kronecker, pd_trace eta heta, mul_one]
  simp only [trace, diag_apply, G_apply] at e1
  simpa [blk] using e1

/-- `(id ⊗ f)(ψψ*)` in terms of the dilated vector. -/
lemma idT_f (U : Matrix.unitaryGroup (Q × E) ℂ) (eta : EuclideanSpace ℂ E)
    (psi : EuclideanSpace ℂ (R × Q)) (r r' : R) (q t : Q) :
    dilationChannel U eta (of fun i i' => psi (r, i) * conj (psi (r', i'))) q t =
      ∑ e, dilatedVector U eta psi (r, (q, e)) * conj (dilatedVector U eta psi (r', (t, e))) := by
  show traceRight ((U : Matrix (Q × E) (Q × E) ℂ) * Matrix.kronecker (blk psi r r') (pureDensity eta) *
      (U : Matrix (Q × E) (Q × E) ℂ)ᴴ) q t = _
  simp only [traceRight, of_apply, G_apply]

section kets
variable {Q : Type*} [Fintype Q]

lemma ketBra_mul (a b c d : EuclideanSpace ℂ Q) :
    ketBra a b * ketBra c d = (∑ x, conj (b x) * c x) • ketBra a d := by
  ext p q
  simp only [ketBra, mul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

lemma ketBra_ct (a b : EuclideanSpace ℂ Q) : (ketBra a b)ᴴ = ketBra b a := by
  ext p q; simp [ketBra, conjTranspose_apply, mul_comm]

lemma act_ketBra (a b w : EuclideanSpace ℂ Q) :
    act (ketBra a b) w = (∑ x, conj (b x) * w x) • a := by
  ext p
  simp only [act, ketBra, PiLp.toLp_apply, mulVec, dotProduct, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

lemma act_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix Q Q ℂ) (w : EuclideanSpace ℂ Q) :
    act (∑ i ∈ s, A i) w = ∑ i ∈ s, act (A i) w := by
  ext p; simp [act, Matrix.sum_mulVec, Finset.sum_apply]

lemma act_sub (A B : Matrix Q Q ℂ) (w : EuclideanSpace ℂ Q) :
    act (A - B) w = act A w - act B w := by
  ext p; simp [act, Matrix.sub_mulVec]

lemma act_one (w : EuclideanSpace ℂ Q) : act (1 : Matrix Q Q ℂ) w = w := by
  ext p; simp [act]

variable {k l : ℕ} (beta : Fin k → EuclideanSpace ℂ Q) (phi : Fin k × Fin l → EuclideanSpace ℂ Q)

lemma Q0_act (hphi : Orthonormal ℂ phi) (b : Fin k × Fin l) :
    act (∑ a, pureDensity (phi a)) (phi b) = phi b := by
  rw [act_sum]
  simp only [show ∀ a, pureDensity (phi a) = ketBra (phi a) (phi a) from fun _ => rfl, act_ketBra,
    (on_iff phi).1 hphi, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma Q0_ct : (∑ a, pureDensity (phi a))ᴴ = ∑ a, pureDensity (phi a) := by
  rw [conjTranspose_sum]
  exact Finset.sum_congr rfl fun a _ => ketBra_ct _ _

lemma Q0_sq (hphi : Orthonormal ℂ phi) :
    (∑ a, pureDensity (phi a)) * (∑ a, pureDensity (phi a)) = ∑ a, pureDensity (phi a) := by
  simp only [show ∀ a, pureDensity (phi a) = ketBra (phi a) (phi a) from fun _ => rfl,
    Finset.sum_mul, Finset.mul_sum, ketBra_mul, (on_iff phi).1 hphi, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma Pi_ct : (1 - ∑ a, pureDensity (phi a))ᴴ = 1 - ∑ a, pureDensity (phi a) := by
  rw [conjTranspose_sub, conjTranspose_one, Q0_ct]

lemma Pi_sq (hphi : Orthonormal ℂ phi) :
    (1 - ∑ a, pureDensity (phi a)) * (1 - ∑ a, pureDensity (phi a)) =
      1 - ∑ a, pureDensity (phi a) := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Q0_sq phi hphi]; simp

lemma Pi_act (hphi : Orthonormal ℂ phi) (b : Fin k × Fin l) :
    act (1 - ∑ a, pureDensity (phi a)) (phi b) = 0 := by
  rw [act_sub, act_one, Q0_act phi hphi, sub_self]

lemma A_act (hphi : Orthonormal ℂ phi) (j : Fin l) (i : Fin k) (t : Fin l) :
    act (recoveryOperators beta phi (some j)) (phi (i, t)) = if j = t then beta i else 0 := by
  simp only [recoveryOperators, act_sum, act_ketBra, (on_iff phi).1 hphi, Prod.mk.injEq, ite_smul,
    one_smul, zero_smul]
  by_cases h : j = t
  · subst h; simp
  · simp [h]

lemma A_kraus (hbeta : Orthonormal ℂ beta) (hphi : Orthonormal ℂ phi) :
    IsKrausFamily (recoveryOperators beta phi) := by
  unfold IsKrausFamily
  rw [Fintype.sum_option]
  have h1 : ∀ j : Fin l, (recoveryOperators beta phi (some j))ᴴ * recoveryOperators beta phi (some j) =
      ∑ i, pureDensity (phi (i, j)) := by
    intro j
    simp only [recoveryOperators, conjTranspose_sum, ketBra_ct, Finset.sum_mul, Finset.mul_sum,
      ketBra_mul, (on_iff beta).1 hbeta, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  simp only [h1]
  rw [show (∑ j : Fin l, ∑ i : Fin k, pureDensity (phi (i, j))) = ∑ a, pureDensity (phi a) by
    rw [Finset.sum_comm, ← Fintype.sum_prod_type']]
  show (1 - ∑ a, pureDensity (phi a))ᴴ * (1 - ∑ a, pureDensity (phi a)) + _ = 1
  rw [Pi_ct, Pi_sq phi hphi, sub_add_cancel]

end kets

section kr
variable {Q : Type*} [Fintype Q]

lemma act_smul (A : Matrix Q Q ℂ) (c : ℂ) (w : EuclideanSpace ℂ Q) :
    act A (c • w) = c • act A w := by
  ext p; simp [act, Matrix.mulVec_smul]

lemma act_vsum {ι : Type*} (s : Finset ι) (A : Matrix Q Q ℂ) (w : ι → EuclideanSpace ℂ Q) :
    act A (∑ i ∈ s, w i) = ∑ i ∈ s, act A (w i) := by
  ext p; simp [act, WithLp.ofLp_sum, Matrix.mulVec_sum, Finset.sum_apply]

lemma kraus_rank1 {K : Type*} [Fintype K] (A : K → Matrix Q Q ℂ) (u u' : EuclideanSpace ℂ Q)
    (x y : Q) :
    krausApply A (of fun q t => u q * conj (u' t)) x y =
      ∑ o, act (A o) u x * conj (act (A o) u' y) := by
  simp only [krausApply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [mul3_entry]
  simp only [act, PiLp.toLp_apply, mulVec, dotProduct, of_apply, map_sum, map_mul,
    Finset.sum_mul_sum, RCLike.star_def]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => ?_
  ring

lemma kraus_sum {K ι : Type*} [Fintype K] (A : K → Matrix Q Q ℂ) (s : Finset ι)
    (X : ι → Matrix Q Q ℂ) : krausApply A (∑ e ∈ s, X e) = ∑ e ∈ s, krausApply A (X e) := by
  simp only [krausApply, Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_comm

end kr

lemma marg {ι A B : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    (Ψ : A × B → ℂ) (s : ι → ℝ) (v : ι → EuclideanSpace ℂ A) (hv : Orthonormal ℂ v)
    (w : ι → EuclideanSpace ℂ B) (h : ∀ a b, Ψ (a, b) = ∑ i, (s i : ℂ) * (v i a * w i b))
    (b b' : B) :
    ∑ a, Ψ (a, b) * conj (Ψ (a, b')) = ∑ i, ((s i ^ 2 : ℝ) : ℂ) * (w i b * conj (w i b')) := by
  have e1 : ∀ a, Ψ (a, b) * conj (Ψ (a, b')) = ∑ i, ∑ j, ((s i : ℂ) * (v i a * w i b)) *
      ((s j : ℂ) * (conj (v j a) * conj (w j b'))) := by
    intro a
    rw [h, h, map_sum, Finset.sum_mul_sum]
    simp only [map_mul, Complex.conj_ofReal]
  simp only [e1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have hi : ∀ j, ∑ a, (s i : ℂ) * (v i a * w i b) * ((s j : ℂ) * (conj (v j a) * conj (w j b'))) =
      (s i : ℂ) * w i b * ((s j : ℂ) * conj (w j b')) * ∑ a, conj (v j a) * v i a := by
    intro j; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
  simp only [hi, (on_iff v).1 hv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  push_cast; ring

end X6SR


/-! X6: Gap20.P06.schmidt_recovery_construction. -/

open scoped ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6SR
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Gap20.P06

attribute [local instance] Classical.propDecidable Classical.decEq

theorem main {R Q E : Type*}
    [Fintype R] [Fintype Q] [Fintype E] [Nonempty R] [Nonempty Q] [Nonempty E]
    (rho : Matrix Q Q ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (R × Q)) (hpsi : ‖psi‖ = 1)
    (hpur : traceLeft (pureDensity psi) = rho)
    (f : Superop Q Q) (hf : IsChannel f)
    (U : Matrix.unitaryGroup (Q × E) ℂ) (eta : EuclideanSpace ℂ E)
    (heta : ‖eta‖ = 1) (hdil : ∀ X, f X = dilationChannel U eta X)
    (heq : (vnEntropy (f rho) - vnEntropy (idTensorSuperop f (pureDensity psi))) = vnEntropy rho) :
    ∃ (k l : ℕ) (lam : Fin k → ℝ) (mu : Fin l → ℝ)
      (alpha : Fin k → EuclideanSpace ℂ R) (beta : Fin k → EuclideanSpace ℂ Q)
      (gamma : Fin l → EuclideanSpace ℂ E)
      (phi : Fin k × Fin l → EuclideanSpace ℂ Q),
      0 < k ∧ 0 < l ∧ (∀ i, 0 < lam i) ∧ (∀ j, 0 < mu j) ∧
      (∑ i, lam i) = 1 ∧ (∑ j, mu j) = 1 ∧
      Orthonormal ℂ alpha ∧ Orthonormal ℂ beta ∧ Orthonormal ℂ gamma ∧
      Orthonormal ℂ phi ∧
      psi = ∑ i, (Real.sqrt (lam i) : ℂ) • tensorVec (alpha i) (beta i) ∧
      rho = ∑ i, (lam i : ℂ) • pureDensity (beta i) ∧
      environmentOutput U eta rho = ∑ j, (mu j : ℂ) • pureDensity (gamma j) ∧
      dilatedVector U eta psi =
        ∑ i, ∑ j, (Real.sqrt (lam i * mu j) : ℂ) •
          tensorVec (alpha i) (tensorVec (phi (i, j)) (gamma j)) ∧
      (let Pi := (1 - ∑ a, pureDensity (phi a))
       let A := recoveryOperators beta phi
       let d := krausApply A
       Piᴴ = Pi ∧ Pi * Pi = Pi ∧
       (∀ i j, act Pi (phi (i, j)) = 0) ∧
       (∀ i j t, act (A (some j)) (phi (i, t)) = if j = t then beta i else 0) ∧
       IsKrausFamily A ∧ IsChannel d ∧
       middleSuperop (R := R) (E := E) d (pureDensity (dilatedVector U eta psi)) =
         appendEnvironment (pureDensity psi) (environmentOutput U eta rho) ∧
       idTensorSuperop (R := R) (d ∘ f) (pureDensity psi) = pureDensity psi) := by
  have hprod := ((coherentInformation_bound_and_equality rho hrho psi hpsi hpur f hf U eta heta
    hdil).2).1 heq
  set Φ := dilatedVector U eta psi with hΦ
  set ρR := traceRight (pureDensity psi) with hρRdef
  set ρE := environmentOutput U eta rho with hρEdef
  -- the reference marginal
  have hρR_e : ∀ r r', ρR r r' = ∑ q, psi (r, q) * conj (psi (r', q)) := fun r r' => by
    simp [ρR, traceRight, pureDensity]
  have hρR_psd : ρR.PosSemidef := by
    have : ρR = (of fun r q => psi (r, q)) * (of fun r q => psi (r, q))ᴴ := by
      ext r r'; rw [hρR_e]; simp [mul_apply, RCLike.star_def]
    rw [this]; exact posSemidef_self_mul_conjTranspose _
  have hρR_tr : ρR.trace = 1 := by
    rw [← pd_trace psi hpsi]
    simp only [trace, diag_apply, hρR_e, Fintype.sum_prod_type, pureDensity, of_apply]
  obtain ⟨k, lam, alpha, hk, hlam, hlam1, halpha, hρR⟩ := spec_pos hρR_psd hρR_tr
  have hρR_e2 : ∀ r r', ρR r r' = ∑ i, (lam i : ℂ) * (alpha i r * conj (alpha i r')) := by
    intro r r'; rw [hρR]; simp [Matrix.sum_apply, pureDensity]
  obtain ⟨beta, hbeta, hpsiS⟩ := purif psi lam hlam alpha halpha
    (fun r r' => (hρR_e r r').symm.trans (hρR_e2 r r'))
  -- the environment marginal
  have hrefE : ∀ r e r' e', ∑ q, Φ (r, (q, e)) * conj (Φ (r', (q, e'))) = ρR r r' * ρE e e' := by
    intro r e r' e'
    have := congrFun (congrFun hprod (r, e)) (r', e')
    simpa [referenceEnvironment, pureDensity, Matrix.kronecker, kroneckerMap_apply] using this
  have hρE_e : ∀ e e', ρE e e' = ∑ r, ∑ q, Φ (r, (q, e)) * conj (Φ (r, (q, e'))) := by
    intro e e'
    simp only [hrefE, ← Finset.sum_mul]
    have : ∑ r, ρR r r = 1 := hρR_tr
    rw [this, one_mul]
  have hρE_psd : ρE.PosSemidef := by
    have : ρE = (of fun e (z : R × Q) => Φ (z.1, (z.2, e))) *
        (of fun e (z : R × Q) => Φ (z.1, (z.2, e)))ᴴ := by
      ext e e'; rw [hρE_e]; simp [mul_apply, RCLike.star_def, Fintype.sum_prod_type]
    rw [this]; exact posSemidef_self_mul_conjTranspose _
  have hρE_tr : ρE.trace = 1 := by
    rw [← hρR_tr]
    simp only [trace, diag_apply, hρE_e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm, ← Fintype.sum_prod_type', tr_G U eta heta psi r r, hρR_e]
  obtain ⟨l, mu, gamma, hl, hmu, hmu1, hgamma, hρE⟩ := spec_pos hρE_psd hρE_tr
  have hρE_e2 : ∀ e e', ρE e e' = ∑ j, (mu j : ℂ) * (gamma j e * conj (gamma j e')) := by
    intro e e'; rw [hρE]; simp [Matrix.sum_apply, pureDensity]
  -- the joint purification of `ρ_R ⊗ ρ_E`
  set c : Fin k × Fin l → ℝ := fun p => lam p.1 * mu p.2 with hc
  have hcpos : ∀ p, 0 < c p := fun p => mul_pos (hlam p.1) (hmu p.2)
  set v : Fin k × Fin l → EuclideanSpace ℂ (R × E) := fun p => tensorVec (alpha p.1) (gamma p.2)
  have hv : Orthonormal ℂ v := by
    rw [on_iff]; rintro ⟨i, j⟩ ⟨i', j'⟩
    have e1 : ∑ z : R × E, conj (v (i, j) z) * v (i', j') z =
        (∑ r, conj (alpha i r) * alpha i' r) * ∑ e, conj (gamma j e) * gamma j' e := by
      rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun e _ => ?_
      simp only [v, tensorVec, PiLp.toLp_apply, map_mul]; ring
    rw [e1, (on_iff alpha).1 halpha, (on_iff gamma).1 hgamma]
    by_cases h1 : i = i' <;> by_cases h2 : j = j' <;> simp [h1, h2]
  set Ψ' : EuclideanSpace ℂ ((R × E) × Q) := WithLp.toLp 2 fun z => Φ (z.1.1, (z.2, z.1.2))
  obtain ⟨phi, hphi, hΦS⟩ := purif Ψ' c hcpos v hv (by
    rintro ⟨r, e⟩ ⟨r', e'⟩
    show ∑ q, Φ (r, (q, e)) * conj (Φ (r', (q, e'))) = _
    rw [hrefE, hρR_e2, hρE_e2, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [c, v, tensorVec, PiLp.toLp_apply, map_mul]; push_cast; ring)
  have hΦS' : ∀ r q e, Φ (r, (q, e)) =
      ∑ i, ∑ j, (Real.sqrt (lam i * mu j) : ℂ) * (alpha i r * gamma j e * phi (i, j) q) := by
    intro r q e
    have := hΦS (r, e) q
    simp only [Ψ', PiLp.toLp_apply] at this
    rw [this, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [c, v, tensorVec, PiLp.toLp_apply]
  -- the recovery map on the dilated vector
  set A := recoveryOperators beta phi with hA
  set u : R → E → EuclideanSpace ℂ Q := fun r e => WithLp.toLp 2 fun q => Φ (r, (q, e))
  have hu : ∀ r e, u r e = ∑ i, ∑ j,
      ((Real.sqrt (lam i * mu j) : ℂ) * (alpha i r * gamma j e)) • phi (i, j) := by
    intro r e; ext q
    simp only [u, PiLp.toLp_apply, hΦS', WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hact_none : ∀ r e, act (A none) (u r e) = 0 := by
    intro r e
    simp only [hu, act_vsum, act_smul, A, recoveryOperators, Pi_act phi hphi, smul_zero,
      Finset.sum_const_zero]
  have hact_some : ∀ r e j, act (A (some j)) (u r e) =
      ((Real.sqrt (mu j) : ℂ) * gamma j e) • (WithLp.toLp 2 fun q => psi (r, q)) := by
    intro r e j
    simp only [hu, act_vsum, act_smul, A, A_act beta phi hphi, smul_ite, smul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ext q
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, PiLp.toLp_apply,
      hpsiS r q, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.sqrt_mul (hlam i).le]; push_cast; ring
  have dkey : ∀ r e r' e' x y,
      krausApply A (of fun q t => Φ (r, (q, e)) * conj (Φ (r', (t, e')))) x y =
        psi (r, x) * conj (psi (r', y)) * ρE e e' := by
    intro r e r' e' x y
    rw [show (of fun q t => Φ (r, (q, e)) * conj (Φ (r', (t, e')))) =
      of fun q t => u r e q * conj (u r' e' t) from rfl, kraus_rank1, Fintype.sum_option, hact_none, hact_none, hρE_e2, Finset.mul_sum]
    simp only [hact_some, PiLp.zero_apply, zero_mul, zero_add, PiLp.smul_apply, PiLp.toLp_apply,
      smul_eq_mul, map_mul, Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hm : (Real.sqrt (mu j) : ℂ) * (Real.sqrt (mu j) : ℂ) = mu j := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hmu j).le]
    linear_combination (gamma j e * psi (r, x) * (conj (gamma j e') * conj (psi (r', y)))) * hm
  refine ⟨k, l, lam, mu, alpha, beta, gamma, phi, hk, hl, hlam, hmu, hlam1, hmu1, halpha, hbeta,
    hgamma, hphi, ?_, ?_, hρE, ?_, ?_⟩
  · ext ⟨r, q⟩
    rw [hpsiS r q]
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, tensorVec,
      PiLp.toLp_apply]
  · rw [← hpur]
    ext q q'
    have := marg (fun z => psi z) (fun i => Real.sqrt (lam i)) alpha halpha beta hpsiS q q'
    simp only [traceLeft, pureDensity, of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.sq_sqrt (hlam i).le]
  · ext ⟨r, q, e⟩
    rw [hΦS' r q e]
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, tensorVec,
      PiLp.toLp_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  intro Pi A' d
  refine ⟨Pi_ct phi, Pi_sq phi hphi, fun i j => Pi_act phi hphi (i, j),
    fun i j t => A_act beta phi hphi j i t,
    A_kraus beta phi hbeta hphi, ?_, ?_, ?_⟩
  · refine ⟨l + 1, fun n => A' (finSuccEquiv l n), ?_, fun ρ => ?_⟩
    · unfold IsKrausFamily
      rw [(finSuccEquiv l).sum_comp (fun o => (A' o)ᴴ * A' o)]
      exact A_kraus beta phi hbeta hphi
    · show krausApply A' ρ = _
      unfold krausApply
      exact ((finSuccEquiv l).sum_comp (fun o => A' o * ρ * (A' o)ᴴ)).symm
  · ext a b
    exact (dkey a.1 a.2.2 b.1 b.2.2 a.2.1 b.2.1)
  · ext ⟨r, x⟩ ⟨r', y⟩
    show d (f (of fun i i' => psi (r, i) * conj (psi (r', i')))) x y = psi (r, x) * conj (psi (r', y))
    have hF : f (of fun i i' => psi (r, i) * conj (psi (r', i'))) =
        ∑ e, of fun q t => Φ (r, (q, e)) * conj (Φ (r', (t, e))) := by
      ext q t; rw [hdil, idT_f, Matrix.sum_apply]; rfl
    rw [hF]
    show krausApply A (∑ e, _) x y = _
    rw [kraus_sum, Matrix.sum_apply]
    simp only [dkey, ← Finset.mul_sum]
    have : ∑ e, ρE e e = 1 := hρE_tr
    rw [this, mul_one]

end X6SR


/-! X6: unitary dilation of a Kraus channel (for Gap20.P06.recovery_uniform_on_support). -/

open scoped ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6SR
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Gap20.P06

attribute [local instance] Classical.propDecidable Classical.decEq

/-- a copy of `Env m` carrying only the classical `DecidableEq` instance. -/
def Env (m : ℕ) : Type := Fin m

instance (m : ℕ) : Fintype (Env m) := inferInstanceAs (Fintype (Fin m))

lemma stine {Q : Type*} [Fintype Q] [Nonempty Q] {m : ℕ} (K : Fin m → Matrix Q Q ℂ)
    (hK : IsKrausFamily K) :
    ∃ (_ : 0 < m) (eta : EuclideanSpace ℂ (Env m)) (U : Matrix.unitaryGroup (Q × Env m) ℂ),
      ‖eta‖ = 1 ∧ ∀ X, krausApply K X = dilationChannel U eta X := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso; subst h
      unfold IsKrausFamily at hK
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hK
      obtain ⟨q⟩ := ‹Nonempty Q›
      have := congrFun (congrFun hK q) q
      simp at this
    · exact h
  set j0 : Env m := (⟨0, hm⟩ : Fin m)
  set s : Set (Q × Env m) := {p | p.2 = j0}
  set vf : Q × Env m → EuclideanSpace ℂ (Q × Env m) :=
    fun p => WithLp.toLp 2 fun z => K z.2 z.1 p.1
  have hKe : ∀ a a', ∑ j, ∑ q, conj (K j q a) * K j q a' = if a = a' then 1 else 0 := by
    intro a a'
    have := congrFun (congrFun hK a) a'
    simp only [Matrix.sum_apply, mul_apply, conjTranspose_apply, one_apply, RCLike.star_def]
      at this
    exact this
  have hv : Orthonormal ℂ (s.domRestrict vf) := by
    rw [orthonormal_iff_ite]
    rintro ⟨p, hp⟩ ⟨p', hp'⟩
    simp only [inner_eq]
    show ∑ z : Q × Env m, conj (K z.2 z.1 p.1) * K z.2 z.1 p'.1 = _
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    show ∑ j : Fin m, ∑ q : Q, conj (K j q p.1) * K j q p'.1 = _
    rw [hKe]
    simp only [s, Set.mem_setOf_eq] at hp hp'
    by_cases h : p.1 = p'.1
    · have : p = p' := Prod.ext h (hp.trans hp'.symm)
      subst this; simp
    · have : ¬ (⟨p, hp⟩ : s) = ⟨p', hp'⟩ := fun e => h (by rw [Subtype.mk.injEq] at e; rw [e])
      simp [h, this]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  set W : Matrix (Q × Env m) (Q × Env m) ℂ := of fun z p => b p z
  have hW : Wᴴ * W = 1 := by
    ext i j
    have h := orthonormal_iff_ite.1 b.orthonormal i j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simp only [W, mul_apply, conjTranspose_apply, of_apply, one_apply]
    rw [← h]
    simp [dotProduct, mul_comm]
  have hWe : ∀ z a, W z (a, j0) = K z.2 z.1 a := by
    intro z a
    simp only [W, of_apply]
    rw [hb (a, j0) rfl]
  refine ⟨hm, EuclideanSpace.single j0 1, ⟨W, Matrix.mem_unitaryGroup_iff'.2 hW⟩,
    by simp, fun X => ?_⟩
  ext q t
  simp only [dilationChannel, conjSuperop, traceRight, of_apply, krausApply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul3_entry, mul3_entry, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.kronecker, kroneckerMap_apply, pureDensity, of_apply, PiLp.single_apply,
    Fintype.sum_prod_type, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, map_one, map_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [apply_ite (starRingEnd ℂ), map_one, map_zero, mul_ite, ite_mul, mul_one, mul_zero,
    zero_mul, one_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, hWe]
  rw [Fintype.sum_eq_single j0 (fun y hy => by simp [hy])]
  simp only [if_true, Finset.sum_ite_eq', Finset.mem_univ, hWe]

end X6SR


/-! X6: fixed points of the recovered channel on the support (Gap20.P06.recovery_uniform_on_support). -/

open scoped ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6SR
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Gap20.P06

attribute [local instance] Classical.propDecidable Classical.decEq

section
variable {Q : Type*} [Fintype Q]

/-- a Kraus map as a linear map. -/
def kL {K : Type*} [Fintype K] (A : K → Matrix Q Q ℂ) : Matrix Q Q ℂ →ₗ[ℂ] Matrix Q Q ℂ where
  toFun := krausApply A
  map_add' X Y := by
    simp only [krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp only [krausApply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, RingHom.id_apply]

lemma ketBra_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (c : ι → ℂ) (u : ι → EuclideanSpace ℂ Q)
    (e : κ → ℂ) (w : κ → EuclideanSpace ℂ Q) :
    ketBra (∑ a, c a • u a) (∑ b, e b • w b) = ∑ a, ∑ b, (c a * conj (e b)) • ketBra (u a) (w b) := by
  ext x y
  simp only [ketBra, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, map_sum,
    map_mul, Finset.sum_mul_sum, Matrix.sum_apply, Matrix.smul_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- expansion in an orthonormal family of a vector in its span. -/
lemma span_expand {k : ℕ} (beta : Fin k → EuclideanSpace ℂ Q) (hbeta : Orthonormal ℂ beta)
    (c : Fin k → ℂ) (v : EuclideanSpace ℂ Q) (hv : v = ∑ i, c i • beta i) :
    v = ∑ a, (∑ x, conj (beta a x) * v x) • beta a := by
  conv_lhs => rw [hv]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [hv]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ i, ∑ x, conj (beta a x) * (c i * beta i x) = c i * ∑ x, conj (beta a x) * beta i x :=
    fun i => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
  simp only [this, (on_iff beta).1 hbeta, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- a linear map fixing all `|β_a⟩⟨β_b|` fixes `|u⟩⟨w|` for `u, w` in the span. -/
lemma fix_span (G : Matrix Q Q ℂ →ₗ[ℂ] Matrix Q Q ℂ) {k : ℕ} (beta : Fin k → EuclideanSpace ℂ Q)
    (hbeta : Orthonormal ℂ beta) (hG : ∀ a b, G (ketBra (beta a) (beta b)) = ketBra (beta a) (beta b))
    (u w : EuclideanSpace ℂ Q) (cu cw : Fin k → ℂ) (hu : u = ∑ i, cu i • beta i)
    (hw : w = ∑ i, cw i • beta i) : G (ketBra u w) = ketBra u w := by
  rw [span_expand beta hbeta cu u hu, span_expand beta hbeta cw w hw, ketBra_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, hG]

end

section
variable {R Q : Type*} [Fintype R] [Fintype Q]

lemma coef {k : ℕ} (lam : Fin k → ℝ) (alpha : Fin k → EuclideanSpace ℂ R) (halpha : Orthonormal ℂ alpha)
    (beta : Fin k → EuclideanSpace ℂ Q) (psi : EuclideanSpace ℂ (R × Q))
    (hpsiS : ∀ r q, psi (r, q) = ∑ i, (Real.sqrt (lam i) : ℂ) * (alpha i r * beta i q)) (a : Fin k)
    (x : Q) : ∑ r, conj (alpha a r) * psi (r, x) = (Real.sqrt (lam a) : ℂ) * beta a x := by
  simp only [hpsiS, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ i, ∑ r, conj (alpha a r) * ((Real.sqrt (lam i) : ℂ) * (alpha i r * beta i x)) =
      (Real.sqrt (lam i) : ℂ) * beta i x * ∑ r, conj (alpha a r) * alpha i r :=
    fun i => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
  simp only [this, (on_iff alpha).1 halpha, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

lemma fix_ket (G : Matrix Q Q ℂ →ₗ[ℂ] Matrix Q Q ℂ) {k : ℕ} (lam : Fin k → ℝ)
    (hlam : ∀ i, 0 < lam i) (alpha : Fin k → EuclideanSpace ℂ R) (halpha : Orthonormal ℂ alpha)
    (beta : Fin k → EuclideanSpace ℂ Q) (psi : EuclideanSpace ℂ (R × Q))
    (hpsiS : ∀ r q, psi (r, q) = ∑ i, (Real.sqrt (lam i) : ℂ) * (alpha i r * beta i q))
    (hfix : ∀ r r', G (of fun i i' => psi (r, i) * conj (psi (r', i'))) =
      of fun i i' => psi (r, i) * conj (psi (r', i'))) (a b : Fin k) :
    G (ketBra (beta a) (beta b)) = ketBra (beta a) (beta b) := by
  set T := ∑ r, ∑ r', (conj (alpha a r) * alpha b r') •
    (of fun i i' => psi (r, i) * conj (psi (r', i')) : Matrix Q Q ℂ)
  have hT : T = ((Real.sqrt (lam a) : ℂ) * (Real.sqrt (lam b) : ℂ)) • ketBra (beta a) (beta b) := by
    ext x y
    have e1 := coef lam alpha halpha beta psi hpsiS a x
    have e2 := congrArg conj (coef lam alpha halpha beta psi hpsiS b y)
    simp only [map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal] at e2
    simp only [T, Matrix.sum_apply, Matrix.smul_apply, of_apply, smul_eq_mul, ketBra]
    have : ∀ r r', conj (alpha a r) * alpha b r' * (psi (r, x) * conj (psi (r', y))) =
        (conj (alpha a r) * psi (r, x)) * (alpha b r' * conj (psi (r', y))) := fun r r' => by ring
    simp only [this, ← Finset.sum_mul_sum, e1, e2]
    ring
  have hGT : G T = T := by
    simp only [T, map_sum, map_smul, hfix]
  rw [hT, map_smul] at hGT
  have hs : ((Real.sqrt (lam a) : ℂ) * (Real.sqrt (lam b) : ℂ)) ≠ 0 := by
    have ha : (Real.sqrt (lam a) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (hlam a)).ne'
    have hb : (Real.sqrt (lam b) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (hlam b)).ne'
    exact mul_ne_zero ha hb
  exact smul_right_injective _ hs hGT

end

lemma gram_mem {ι Q : Type*} [Fintype ι] [Fintype Q] (χ : EuclideanSpace ℂ (ι × Q)) (r : ι) :
    (WithLp.toLp 2 fun q => χ (r, q) : EuclideanSpace ℂ Q) ∈
      LinearMap.range (Matrix.toEuclideanLin (traceLeft (pureDensity χ))) := by
  set W := LinearMap.range (Matrix.toEuclideanLin (traceLeft (pureDensity χ)))
  rw [← Submodule.orthogonal_orthogonal W, Submodule.mem_orthogonal]
  intro u hu
  have h0 := (Submodule.mem_orthogonal W u).1 hu _ (LinearMap.mem_range_self _ u)
  set z : ι → ℂ := fun s => ∑ q, conj (χ (s, q)) * u q
  have hz : inner ℂ (Matrix.toEuclideanLin (traceLeft (pureDensity χ)) u) u = ∑ s, conj (z s) * z s := by
    rw [inner_eq]
    simp only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, mulVec, dotProduct, traceLeft, pureDensity, of_apply,
      z, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs => arg 2; ext q'; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q' _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [hz] at h0
  have hn : ∀ s, conj (z s) * z s = ((Complex.normSq (z s) : ℝ) : ℂ) := fun s => by
    rw [mul_comm, Complex.mul_conj]
  simp only [hn] at h0
  have h1 : ∑ s, Complex.normSq (z s) = 0 := by exact_mod_cast h0
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun s _ => Complex.normSq_nonneg (z s)).1 h1 r
    (Finset.mem_univ _)
  have h3 : z r = 0 := Complex.normSq_eq_zero.1 h2
  rw [inner_eq]
  have : ∑ q, conj (u q) * χ (r, q) = conj (z r) := by
    simp only [z, map_sum, map_mul, Complex.conj_conj]
    exact Finset.sum_congr rfl fun q _ => mul_comm _ _
  simpa [h3] using this

lemma rng_span {Q : Type*} [Fintype Q] {k : ℕ} (lam : Fin k → ℝ) (beta : Fin k → EuclideanSpace ℂ Q)
    (v : EuclideanSpace ℂ Q)
    (hv : v ∈ LinearMap.range (Matrix.toEuclideanLin (∑ i, (lam i : ℂ) • pureDensity (beta i)))) :
    ∃ c : Fin k → ℂ, v = ∑ i, c i • beta i := by
  obtain ⟨w, rfl⟩ := hv
  refine ⟨fun i => (lam i : ℂ) * ∑ x, conj (beta i x) * w x, ?_⟩
  ext q
  simp only [Matrix.toEuclideanLin_apply, PiLp.toLp_apply, mulVec, dotProduct, Matrix.sum_apply,
    Matrix.smul_apply, pureDensity, of_apply, smul_eq_mul, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
  ring

end X6SR


/-! X6: Gap20.P06.recovery_uniform_on_support. -/

open scoped ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6SR
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Gap20.P06

attribute [local instance] Classical.propDecidable Classical.decEq

theorem main2 {R Q : Type*}
    [Fintype R] [Fintype Q] [Nonempty R] [Nonempty Q]
    (rho : Matrix Q Q ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (R × Q)) (hpsi : ‖psi‖ = 1)
    (hpur : traceLeft (pureDensity psi) = rho)
    (f : Superop Q Q) (hf : IsChannel f)
    (heq : (vnEntropy (f rho) - vnEntropy (idTensorSuperop f (pureDensity psi))) = vnEntropy rho) :
    ∃ d : Superop Q Q, IsChannel d ∧
      idTensorSuperop (R := R) (d ∘ f) (pureDensity psi) = pureDensity psi ∧
      (∀ v : EuclideanSpace ℂ Q, ‖v‖ = 1 → v ∈ LinearMap.range (Matrix.toEuclideanLin rho) →
        d (f (pureDensity v)) = pureDensity v) ∧
      (∀ (r : ℕ) (chi : EuclideanSpace ℂ (Fin r × Q)), ‖chi‖ = 1 →
        LinearMap.range (Matrix.toEuclideanLin (traceLeft (pureDensity chi))) =
          LinearMap.range (Matrix.toEuclideanLin rho) →
        idTensorSuperop (R := Fin r) (d ∘ f) (pureDensity chi) = pureDensity chi) := by
  obtain ⟨m, K, hK, hfK⟩ := hf
  obtain ⟨hm, eta, U, heta, hdilK⟩ := stine K hK
  have : Nonempty (Env m) := ⟨(⟨0, hm⟩ : Fin m)⟩
  have hdil : ∀ X, f X = dilationChannel U eta X := fun X => (hfK X).trans (hdilK X)
  obtain ⟨k, l, lam, mu, alpha, beta, gamma, phi, hk, hl, hlam, hmu, hlam1, hmu1, halpha, hbeta,
    hgamma, hphi, hpsiv, hrhov, -, -, hrest⟩ :=
    main rho hrho psi hpsi hpur f ⟨m, K, hK, hfK⟩ U eta heta hdil heq
  obtain ⟨-, -, -, -, -, hdch, -, hid⟩ := hrest
  set A := recoveryOperators beta phi
  set G : Matrix Q Q ℂ →ₗ[ℂ] Matrix Q Q ℂ := (kL A).comp (kL K)
  have hG : ∀ X, (krausApply A ∘ f) X = G X := fun X => by
    simp only [Function.comp_apply, hfK]; rfl
  have hpsiS : ∀ r q, psi (r, q) = ∑ i, (Real.sqrt (lam i) : ℂ) * (alpha i r * beta i q) := by
    intro r q
    rw [hpsiv]
    simp [WithLp.ofLp_sum, Finset.sum_apply, tensorVec]
  have hfix : ∀ r r', G (of fun i i' => psi (r, i) * conj (psi (r', i'))) =
      of fun i i' => psi (r, i) * conj (psi (r', i')) := by
    intro r r'
    ext x y
    have := congrFun (congrFun hid (r, x)) (r', y)
    rw [← hG]
    exact this
  have hket := fix_ket G lam hlam alpha halpha beta psi hpsiS hfix
  have hspan := fix_span G beta hbeta hket
  refine ⟨krausApply A, hdch, hid, ?_, ?_⟩
  · intro v _ hv
    rw [hrhov] at hv
    obtain ⟨c, hc⟩ := rng_span lam beta v hv
    rw [← Function.comp_apply (f := krausApply A), hG]
    exact hspan v v c c hc hc
  · intro r chi _ hran
    ext ⟨s, x⟩ ⟨s', y⟩
    have h1 : ∀ s, ∃ c : Fin k → ℂ, (WithLp.toLp 2 fun q => chi (s, q) : EuclideanSpace ℂ Q) =
        ∑ i, c i • beta i := by
      intro s
      have := gram_mem chi s
      rw [hran, hrhov] at this
      exact rng_span lam beta _ this
    obtain ⟨c, hc⟩ := h1 s
    obtain ⟨c', hc'⟩ := h1 s'
    have := hspan _ _ c c' hc hc'
    show (krausApply A ∘ f) (of fun i i' => chi (s, i) * conj (chi (s', i'))) x y = _
    rw [hG]
    exact congrFun (congrFun this x) y

end X6SR


noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Gap20.P06

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {R Q : Type*}
    [Fintype R] [Fintype Q] [Nonempty R] [Nonempty Q]
    (rho : Matrix Q Q ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (R × Q)) (hpsi : ‖psi‖ = 1)
    (hpur : traceLeft (pureDensity psi) = rho)
    (f : Superop Q Q) (hf : IsChannel f)
    (heq : (vnEntropy (f rho) - vnEntropy (idTensorSuperop f (pureDensity psi))) = vnEntropy rho) :
    ∃ d : Superop Q Q, IsChannel d ∧
      idTensorSuperop (R := R) (d ∘ f) (pureDensity psi) = pureDensity psi ∧
      (∀ v : EuclideanSpace ℂ Q, ‖v‖ = 1 → v ∈ LinearMap.range (Matrix.toEuclideanLin rho) →
        d (f (pureDensity v)) = pureDensity v) ∧
      (∀ (r : ℕ) (chi : EuclideanSpace ℂ (Fin r × Q)), ‖chi‖ = 1 →
        LinearMap.range (Matrix.toEuclideanLin (traceLeft (pureDensity chi))) =
          LinearMap.range (Matrix.toEuclideanLin rho) →
        idTensorSuperop (R := Fin r) (d ∘ f) (pureDensity chi) = pureDensity chi) :=
  X6SR.main2 rho hrho psi hpsi hpur f hf heq
