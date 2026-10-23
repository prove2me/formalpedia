-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P06.schmidt_recovery_construction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T05:39:54.528016+00:00
-- url     : https://prove2.me/submissions/18fe6a48-dc66-4d44-ae1b-4b6f2e52a85c

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


noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Gap20.P06

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {R Q E : Type*}
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
       idTensorSuperop (R := R) (d ∘ f) (pureDensity psi) = pureDensity psi) :=
  X6SR.main rho hrho psi hpsi hpur f hf U eta heta hdil heq
