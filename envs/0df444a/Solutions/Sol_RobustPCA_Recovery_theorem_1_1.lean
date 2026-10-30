-- Prove2me | solution 1 for RobustPCA.Recovery.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T11:53:36.706978+00:00
-- url     : https://prove2.me/submissions/f27dda85-9dff-480a-96c7-720216488c60

import Mathlib
import Definitions.Def_RobustPCA_Recovery_Setup
import Theorems.Thm_RobustPCA_Recovery_sec_7_1_transfer
import Theorems.Thm_RobustPCA_Recovery_theorem_2_3
import Theorems.Thm_RobustPCA_Recovery_theorem_2_2
import Theorems.Thm_RobustPCA_Recovery_eq_2_4
import Theorems.Thm_RobustPCA_Recovery_lemma_2_8
import Theorems.Thm_RobustPCA_Recovery_lemma_2_9

set_option autoImplicit false

open MatrixCompletion

namespace RPCA429

open RobustPCA.Recovery
open scoped BigOperators

/-! ## Projection algebra -/

/-- `∑_k u_k u_kᵀ` as a matrix. -/
noncomputable def projM {n r : ℕ} (u : Fin r → Fin n → ℝ) : RealMatrix n n :=
  fun i a => ∑ k, u k i * u k a

/-- `P_U` as a matrix. -/
noncomputable def PU {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : RealMatrix n n :=
  projM SV.u

/-- `P_V` as a matrix. -/
noncomputable def PV {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : RealMatrix n n :=
  projM SV.v

lemma orth_idem {n r : ℕ} (u : Fin r → Fin n → ℝ)
    (hu : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0) :
    projM u * projM u = projM u := by
  ext i c
  simp only [Matrix.mul_apply, projM]
  have h1 : ∀ a, (∑ k, u k i * u k a) * (∑ l, u l a * u l c) =
      ∑ k, ∑ l, u k i * u l c * (u k a * u l a) := by
    intro a
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]
  have h2 : ∀ l, ∑ a, u k i * u l c * (u k a * u l a) =
      u k i * u l c * (if k = l then 1 else 0) := by
    intro l
    rw [← Finset.mul_sum, hu]
  simp_rw [h2]
  simp

lemma PU_idem {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : PU SV * PU SV = PU SV :=
  orth_idem SV.u SV.u_orthonormal

lemma PV_idem {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) : PV SV * PV SV = PV SV :=
  orth_idem SV.v SV.v_orthonormal

lemma tangent_eq {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X : RealMatrix n n) :
    tangentProjection SV X = PU SV * X + X * PV SV - PU SV * X * PV SV := by
  ext i j
  simp only [tangentProjection, leftSingularProjection, rightSingularProjection,
    twoSidedSingularProjection, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, PU, PV, projM]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_mul]

lemma tangent_add {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X Y : RealMatrix n n) :
    tangentProjection SV (X + Y) = tangentProjection SV X + tangentProjection SV Y := by
  simp only [tangent_eq, Matrix.mul_add, Matrix.add_mul]
  abel

lemma tangent_smul {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (c : ℝ) (X : RealMatrix n n) :
    tangentProjection SV (c • X) = c • tangentProjection SV X := by
  simp only [tangent_eq, Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_add]

lemma tangent_idem {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X : RealMatrix n n) :
    tangentProjection SV (tangentProjection SV X) = tangentProjection SV X := by
  have hA := PU_idem SV
  have hB := PV_idem SV
  have hB' : ∀ Y : RealMatrix n n, Y * PV SV * PV SV = Y * PV SV := by
    intro Y; rw [Matrix.mul_assoc, hB]
  simp only [tangent_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    ← Matrix.mul_assoc, hA, hB']
  abel

lemma tangent_normal {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (X : RealMatrix n n) :
    tangentProjection SV (normalProjection SV X) = 0 := by
  have h : tangentProjection SV (X - tangentProjection SV X) =
      tangentProjection SV X - tangentProjection SV (tangentProjection SV X) := by
    simp only [tangent_eq, Matrix.mul_sub, Matrix.sub_mul]
    abel
  simp only [normalProjection, h, tangent_idem, sub_self]

/-! ## Norm facts -/

lemma spectral_add {n : ℕ} (A B : RealMatrix n n) :
    MatrixCompletion.spectralNorm (A + B) ≤
      MatrixCompletion.spectralNorm A + MatrixCompletion.spectralNorm B := by
  unfold MatrixCompletion.spectralNorm
  rw [map_add, map_add]
  exact norm_add_le _ _

lemma entrySup_nonneg {n : ℕ} (A : RealMatrix n n) : 0 ≤ entrySupNorm A := by
  unfold entrySupNorm
  exact Real.iSup_nonneg (fun i => Real.iSup_nonneg (fun j => abs_nonneg _))

lemma le_entrySup {n : ℕ} (A : RealMatrix n n) (i j : Fin n) : |A i j| ≤ entrySupNorm A := by
  unfold entrySupNorm
  exact le_ciSup_of_le (Finite.bddAbove_range _) i
    (le_ciSup (f := fun j => |A i j|) (Finite.bddAbove_range _) j)

lemma entrySup_add {n : ℕ} (A B : RealMatrix n n) :
    entrySupNorm (A + B) ≤ entrySupNorm A + entrySupNorm B := by
  have h0 : 0 ≤ entrySupNorm A + entrySupNorm B :=
    add_nonneg (entrySup_nonneg A) (entrySup_nonneg B)
  unfold entrySupNorm
  refine Real.iSup_le (fun i => Real.iSup_le (fun j => ?_) h0) h0
  calc |(A + B) i j| = |A i j + B i j| := rfl
    _ ≤ |A i j| + |B i j| := abs_add_le _ _
    _ ≤ entrySupNorm A + entrySupNorm B := add_le_add (le_entrySup A i j) (le_entrySup B i j)

lemma compProj_add {n : ℕ} (Ω : Finset (Fin n × Fin n)) (A B : RealMatrix n n) :
    compProj Ω (A + B) = compProj Ω A + compProj Ω B := by
  ext i j
  simp only [compProj, samplingProjection, Matrix.sub_apply, Matrix.add_apply]
  split_ifs <;> ring

lemma abs_le_frob {n : ℕ} (X : RealMatrix n n) (i j : Fin n) : |X i j| ≤ frobeniusNorm X := by
  unfold frobeniusNorm frobeniusNormSq
  apply Real.abs_le_sqrt
  calc X i j ^ 2 ≤ ∑ j', X i j' ^ 2 :=
        Finset.single_le_sum (f := fun j' => X i j' ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', X i' j' ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', X i' j' ^ 2)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i)

lemma frob_sampling_le {n : ℕ} (Ω : Finset (Fin n × Fin n)) (X : RealMatrix n n) :
    frobeniusNorm (samplingProjection Ω X) ≤ frobeniusNorm X := by
  unfold frobeniusNorm frobeniusNormSq
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro j _
  simp only [samplingProjection]
  split_ifs
  · exact le_rfl
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; exact sq_nonneg _

/-! ## The Neumann-series certificate: `𝒫_Ω W^S = λ E` -/

/-- `𝒜 X = 𝒫_Ω 𝒫_T 𝒫_Ω X` as a linear map. -/
noncomputable def Alin {n r : ℕ} {L0 : RealMatrix n n} (Ω : Finset (Fin n × Fin n))
    (SV : SVD L0 r) : RealMatrix n n →ₗ[ℝ] RealMatrix n n where
  toFun X := samplingProjection Ω (tangentProjection SV (samplingProjection Ω X))
  map_add' X Y := by
    have h1 : samplingProjection Ω (X + Y) = samplingProjection Ω X + samplingProjection Ω Y := by
      ext i j; simp only [samplingProjection, Matrix.add_apply]; split_ifs <;> ring
    rw [h1, tangent_add]
    ext i j; simp only [samplingProjection, Matrix.add_apply]; split_ifs <;> ring
  map_smul' c X := by
    have h1 : samplingProjection Ω (c • X) = c • samplingProjection Ω X := by
      ext i j; simp only [samplingProjection, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> ring
    rw [h1, tangent_smul]
    ext i j; simp only [samplingProjection, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

lemma PTOpNormLe_mono {n r : ℕ} {L0 : RealMatrix n n} {Ω : Finset (Fin n × Fin n)}
    {SV : SVD L0 r} {σ τ : ℝ} (h : PTOpNormLe Ω SV σ) (hστ : σ ≤ τ) : PTOpNormLe Ω SV τ := by
  intro X
  have hX : 0 ≤ frobeniusNorm X := Real.sqrt_nonneg _
  exact (h X).trans (mul_le_mul_of_nonneg_right hστ hX)

lemma Alin_bound {n r : ℕ} {L0 : RealMatrix n n} {Ω : Finset (Fin n × Fin n)}
    {SV : SVD L0 r} {σ : ℝ} (hσ0 : 0 ≤ σ) (h : PTOpNormLe Ω SV σ) (X : RealMatrix n n) :
    frobeniusNorm (Alin Ω SV X) ≤ σ * frobeniusNorm X := by
  show frobeniusNorm (samplingProjection Ω (tangentProjection SV (samplingProjection Ω X))) ≤ _
  exact (h _).trans (mul_le_mul_of_nonneg_left (frob_sampling_le Ω X) hσ0)

lemma Alin_iter_bound {n r : ℕ} {L0 : RealMatrix n n} {Ω : Finset (Fin n × Fin n)}
    {SV : SVD L0 r} {σ : ℝ} (hσ0 : 0 ≤ σ) (h : PTOpNormLe Ω SV σ) (E : RealMatrix n n) (k : ℕ) :
    frobeniusNorm ((Alin Ω SV)^[k] E) ≤ σ ^ k * frobeniusNorm E := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    calc frobeniusNorm (Alin Ω SV ((Alin Ω SV)^[k] E))
        ≤ σ * frobeniusNorm ((Alin Ω SV)^[k] E) := Alin_bound hσ0 h _
      _ ≤ σ * (σ ^ k * frobeniusNorm E) := mul_le_mul_of_nonneg_left ih hσ0
      _ = σ ^ (k + 1) * frobeniusNorm E := by ring

lemma iter_summable {n r : ℕ} {L0 : RealMatrix n n} {Ω : Finset (Fin n × Fin n)}
    {SV : SVD L0 r} {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (h : PTOpNormLe Ω SV σ)
    (E : RealMatrix n n) : Summable (fun k => (Alin Ω SV)^[k] E) := by
  refine Pi.summable.2 (fun i => Pi.summable.2 (fun j => ?_))
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hσ0 hσ1).mul_right
    (frobeniusNorm E)) (fun k => ?_)
  rw [Real.norm_eq_abs]
  exact (abs_le_frob _ i j).trans (Alin_iter_bound hσ0 h E k)

/-- evaluation at an entry -/
def evL {n : ℕ} (i j : Fin n) : RealMatrix n n →ₗ[ℝ] ℝ where
  toFun X := X i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma entry_tsum {n : ℕ} {f : ℕ → RealMatrix n n} (hf : Summable f) (i j : Fin n) :
    (∑' k, f k) i j = ∑' k, f k i j :=
  ((hf.hasSum.map (evL i j) (LinearMap.continuous_of_finiteDimensional _)).tsum_eq).symm

lemma sampling_WS {n r : ℕ} {L0 : RealMatrix n n} (lam : ℝ) (Ω : Finset (Fin n × Fin n))
    (SV : SVD L0 r) (E : RealMatrix n n) (hE : samplingProjection Ω E = E)
    (hΩ : ∃ σ < 1 / 2, PTOpNormLe Ω SV σ) :
    samplingProjection Ω (WS lam Ω SV E) = lam • E := by
  obtain ⟨σ, hσ, hPT⟩ := hΩ
  have hPT' : PTOpNormLe Ω SV (max σ 0) := PTOpNormLe_mono hPT (le_max_left _ _)
  have hσ0 : (0 : ℝ) ≤ max σ 0 := le_max_right _ _
  have hσ1 : max σ 0 < 1 := max_lt (by linarith) (by norm_num)
  set A := Alin Ω SV with hAdef
  have hfun : (fun X => samplingProjection Ω (tangentProjection SV (samplingProjection Ω X))) =
      (A : RealMatrix n n → RealMatrix n n) := rfl
  have hs : Summable (fun k => A^[k] E) := iter_summable hσ0 hσ1 hPT' E
  set T := ∑' k : ℕ, A^[k] E with hT
  have hWS : WS lam Ω SV E = lam • normalProjection SV T := by
    rw [hT]; simp only [WS, hfun]
  -- every iterate is supported on Ω
  have hsupp : ∀ k, samplingProjection Ω (A^[k] E) = A^[k] E := by
    intro k
    cases k with
    | zero => simpa using hE
    | succ k =>
      rw [Function.iterate_succ_apply']
      show samplingProjection Ω (samplingProjection Ω _) = samplingProjection Ω _
      ext i j; simp only [samplingProjection]; split_ifs <;> rfl
  have hTsupp : samplingProjection Ω T = T := by
    ext i j
    simp only [samplingProjection]
    split_ifs with hij
    · rfl
    · rw [hT, entry_tsum hs]
      have : ∀ k, (A^[k] E) i j = 0 := by
        intro k
        have := congrFun (congrFun (hsupp k) i) j
        simp only [samplingProjection, if_neg hij] at this
        exact this.symm
      simp [this]
  have hcont : Continuous (A : RealMatrix n n → RealMatrix n n) :=
    LinearMap.continuous_of_finiteDimensional A
  have hAT : A T = ∑' k : ℕ, A^[k + 1] E := by
    have h1 := (hs.hasSum.map A hcont).tsum_eq
    rw [hT, ← h1]
    congr 1
    funext k
    simp only [Function.comp_apply, Function.iterate_succ_apply']
  have hTsplit : T = E + A T := by
    rw [hAT, hT, hs.tsum_eq_zero_add]
    simp
  have hPTT : samplingProjection Ω (tangentProjection SV T) = A T := by
    show _ = samplingProjection Ω (tangentProjection SV (samplingProjection Ω T))
    rw [hTsupp]
  rw [hWS]
  ext i j
  have e1 := congrFun (congrFun hPTT i) j
  have e2 := congrFun (congrFun hTsplit i) j
  have e3 := congrFun (congrFun hTsupp i) j
  simp only [samplingProjection, normalProjection, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.add_apply, smul_eq_mul] at e1 e2 e3 ⊢
  have e4 := congrFun (congrFun hE i) j
  simp only [samplingProjection] at e4
  split_ifs at e1 e3 e4 ⊢ with hij
  · rw [e1, show T i j - A T i j = E i j by linarith]
  · rw [← e4]; ring

/-! ## The golfing law is the Bernoulli law of `Ω` -/

lemma prod_ite_univ {α : Type*} [Fintype α] [DecidableEq α] (B : Finset α) (a b : ℝ) :
    ∏ x, (if x ∈ B then a else b) = a ^ B.card * b ^ (Fintype.card α - B.card) := by
  rw [← Finset.prod_mul_prod_compl B]
  have h1 : ∏ x ∈ B, (if x ∈ B then a else b) = ∏ x ∈ B, a :=
    Finset.prod_congr rfl (fun x hx => by simp [hx])
  have h2 : ∏ x ∈ Bᶜ, (if x ∈ B then a else b) = ∏ x ∈ Bᶜ, b :=
    Finset.prod_congr rfl (fun x hx => by rw [Finset.mem_compl] at hx; simp [hx])
  rw [h1, h2, Finset.prod_const, Finset.prod_const, Finset.card_compl]

lemma bw_eq_prod {N : ℕ} (p : ℝ) (A : Finset (Fin N × Fin N)) :
    bernoulliObservationWeight p A = ∏ x, (if x ∈ A then p else 1 - p) := by
  unfold bernoulliObservationWeight
  rw [prod_ite_univ]

lemma hsum_one (j0 : ℕ) (q : ℝ) :
    ∑ B : Finset (Fin j0), ∏ j, (if j ∈ B then q else 1 - q) = 1 := by
  have h := Finset.sum_pow_mul_eq_add_pow q (1 - q) (Finset.univ : Finset (Fin j0))
  rw [Finset.powerset_univ, Finset.card_univ, show q + (1 - q) = 1 by ring, one_pow] at h
  simp_rw [prod_ite_univ]
  exact h

lemma bw_sum_one {N : ℕ} (p : ℝ) :
    ∑ A : Finset (Fin N × Fin N), bernoulliObservationWeight p A = 1 := by
  have h := Finset.sum_pow_mul_eq_add_pow p (1 - p) (Finset.univ : Finset (Fin N × Fin N))
  rw [Finset.powerset_univ, Finset.card_univ, show p + (1 - p) = 1 by ring, one_pow] at h
  exact h

lemma bw_nonneg {N : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset (Fin N × Fin N)) :
    0 ≤ bernoulliObservationWeight p A := by
  unfold bernoulliObservationWeight
  exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

/-- transpose of a family of sets -/
def transposeEquiv (X : Type) [Fintype X] [DecidableEq X] (j0 : ℕ) :
    (Fin j0 → Finset X) ≃ (X → Finset (Fin j0)) where
  toFun Ωs x := Finset.univ.filter (fun j => x ∈ Ωs j)
  invFun g j := Finset.univ.filter (fun x => j ∈ g x)
  left_inv Ωs := by funext j; ext x; simp
  right_inv g := by funext x; ext j; simp

lemma golf_couple {n : ℕ} (j0 : ℕ) (q : ℝ) (f : Finset (Fin n × Fin n) → ℝ) :
    ∑ Ωs : Fin j0 → Finset (Fin n × Fin n),
        (∏ j, bernoulliObservationWeight q (Ωs j)) * f (golfOmega Ωs) =
      ∑ Ω : Finset (Fin n × Fin n), bernoulliObservationWeight ((1 - q) ^ j0) Ω * f Ω := by
  let h : Finset (Fin j0) → ℝ := fun B => ∏ j, (if j ∈ B then q else 1 - q)
  have hB : ∑ B, h B = 1 := hsum_one j0 q
  have h0 : h ∅ = (1 - q) ^ j0 := by simp [h]
  -- rewrite the left side through the transpose
  have key : ∀ Ωs : Fin j0 → Finset (Fin n × Fin n),
      (∏ j, bernoulliObservationWeight q (Ωs j)) * f (golfOmega Ωs) =
        (∏ x, h (transposeEquiv (Fin n × Fin n) j0 Ωs x)) *
          f (Finset.univ.filter (fun x => transposeEquiv (Fin n × Fin n) j0 Ωs x = ∅)) := by
    intro Ωs
    congr 1
    · simp only [bw_eq_prod, h, transposeEquiv, Equiv.coe_fn_mk]
      rw [Finset.prod_comm]
      refine Finset.prod_congr rfl (fun x _ => Finset.prod_congr rfl (fun j _ => ?_))
      simp
    · congr 1
      ext x
      simp [golfOmega, transposeEquiv, Finset.eq_empty_iff_forall_notMem]
  rw [Finset.sum_congr rfl (fun Ωs _ => key Ωs)]
  rw [(transposeEquiv (Fin n × Fin n) j0).sum_comp (fun g =>
      (∏ x, h (g x)) * f (Finset.univ.filter (fun x => g x = ∅)))]
  -- expand f
  have hf : ∀ g : (Fin n × Fin n) → Finset (Fin j0),
      (∏ x, h (g x)) * f (Finset.univ.filter (fun x => g x = ∅)) =
        ∑ Ω : Finset (Fin n × Fin n), f Ω * ∏ x, (h (g x) * if (g x = ∅ ↔ x ∈ Ω) then 1 else 0) := by
    intro g
    rw [Finset.sum_eq_single (Finset.univ.filter (fun x => g x = ∅))]
    · rw [Finset.prod_mul_distrib]
      have : ∏ x, (if (g x = ∅ ↔ x ∈ Finset.univ.filter (fun x => g x = ∅)) then (1 : ℝ) else 0)
          = 1 := Finset.prod_eq_one (fun x _ => by simp)
      rw [this]; ring
    · intro Ω _ hne
      have : ∃ x, ¬ (g x = ∅ ↔ x ∈ Ω) := by
        by_contra hall
        push_neg at hall
        apply hne
        ext x; simp [hall x]
      obtain ⟨x, hx⟩ := this
      rw [Finset.prod_eq_zero (Finset.mem_univ x) (by simp [hx])]
      ring
    · intro hn; exact absurd (Finset.mem_univ _) hn
  simp_rw [hf]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun Ω _ => ?_)
  rw [← Finset.mul_sum, mul_comm]
  congr 1
  rw [← Fintype.prod_sum (fun x B => h B * if (B = ∅ ↔ x ∈ Ω) then (1 : ℝ) else 0)]
  rw [bw_eq_prod]
  refine Finset.prod_congr rfl (fun x _ => ?_)
  by_cases hx : x ∈ Ω
  · simp only [hx, iff_true, if_true]
    rw [Finset.sum_eq_single ∅]
    · simp [h0]
    · intro B _ hB'; simp [hB']
    · intro hn; exact absurd (Finset.mem_univ _) hn
  · rw [show (∑ B, h B * if (B = ∅ ↔ x ∈ Ω) then (1 : ℝ) else 0) = ∑ B, h B - h ∅ from ?_]
    · simp only [hx, if_false]; rw [hB, h0]
    · have e : ∀ B : Finset (Fin j0), (h B * if (B = ∅ ↔ x ∈ Ω) then (1 : ℝ) else 0) =
          h B - (if B = ∅ then h B else 0) := by
        intro B; by_cases hB' : B = ∅ <;> simp [hB', hx]
      rw [Finset.sum_congr rfl (fun B _ => e B), Finset.sum_sub_distrib, Finset.sum_ite_eq']
      simp

/-! ## Chernoff lower tail of `|Ω|` under `Ber(p)` -/

lemma ber_tail {n : ℕ} (m : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bernoulliEventProb p (fun Ω : Finset (Fin n × Fin n) => Ω.card < m) ≤
      2 ^ m * (1 - p / 2) ^ (n * n) := by
  classical
  unfold bernoulliEventProb
  have hterm : ∀ Ω : Finset (Fin n × Fin n),
      (@ite ℝ ((fun Ω : Finset (Fin n × Fin n) => Ω.card < m) Ω) (Classical.propDecidable _)
        (bernoulliObservationWeight p Ω) 0) ≤
        2 ^ m * ((p / 2) ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n × Fin n) - Ω.card)) := by
    intro Ω
    have hw : 0 ≤ bernoulliObservationWeight p Ω := bw_nonneg hp0 hp1 Ω
    have heq : 2 ^ m * ((p / 2) ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n × Fin n) - Ω.card)) =
        ((2 : ℝ) ^ m / 2 ^ Ω.card) * bernoulliObservationWeight p Ω := by
      unfold bernoulliObservationWeight
      rw [div_pow]
      field_simp
    rw [heq]
    split_ifs with h
    · have h1 : 1 ≤ (2 : ℝ) ^ m / 2 ^ Ω.card := by
        rw [le_div_iff₀ (by positivity), one_mul]
        exact pow_le_pow_right₀ (by norm_num) h.le
      nlinarith
    · exact mul_nonneg (by positivity) hw
  calc _ ≤ ∑ Ω : Finset (Fin n × Fin n),
        2 ^ m * ((p / 2) ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n × Fin n) - Ω.card)) :=
        Finset.sum_le_sum (fun Ω _ => hterm Ω)
    _ = 2 ^ m * (p / 2 + (1 - p)) ^ (n * n) := by
        rw [← Finset.mul_sum]
        congr 1
        have h := Finset.sum_pow_mul_eq_add_pow (p / 2) (1 - p)
          (Finset.univ : Finset (Fin n × Fin n))
        rw [Finset.powerset_univ, Finset.card_univ] at h
        rw [h]
        simp [Fintype.card_prod, Fintype.card_fin]
    _ = 2 ^ m * (1 - p / 2) ^ (n * n) := by congr 2; ring

lemma tail_poly (n m : ℕ) (ρs : ℝ) (hρ : 0 < ρs) (hρ1 : ρs ≤ 1 / 2) (hn : 0 < n)
    (hm : (m : ℝ) ≤ ρs * (n : ℝ) ^ 2) :
    2 ^ m * (1 - 2 * ρs / 2) ^ (n * n) ≤ 120 / (3 / 10 * ρs) ^ 5 * (n : ℝ) ^ (-10 : ℤ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : ((n * n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by push_cast; ring
  have h1 : (1 - 2 * ρs / 2) ^ (n * n) ≤ Real.exp (-ρs * (n : ℝ) ^ 2) := by
    have h := Real.one_sub_le_exp_neg ρs
    calc (1 - 2 * ρs / 2) ^ (n * n) = (1 - ρs) ^ (n * n) := by ring_nf
      _ ≤ (Real.exp (-ρs)) ^ (n * n) := pow_le_pow_left₀ (by linarith) h _
      _ = Real.exp (-ρs * (n : ℝ) ^ 2) := by
          rw [← Real.exp_nat_mul, hN]; ring_nf
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2 : (2 : ℝ) ^ m ≤ Real.exp (ρs * (n : ℝ) ^ 2 * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.2
    nlinarith
  have hl2 := Real.log_two_lt_d9
  have hx : 0 < 3 / 10 * ρs * (n : ℝ) ^ 2 := by positivity
  have h3 : (2 : ℝ) ^ m * (1 - 2 * ρs / 2) ^ (n * n) ≤ Real.exp (-(3 / 10 * ρs * (n : ℝ) ^ 2)) := by
    have hA : 0 ≤ (1 - 2 * ρs / 2) ^ (n * n) := pow_nonneg (by linarith) _
    calc (2 : ℝ) ^ m * (1 - 2 * ρs / 2) ^ (n * n)
        ≤ Real.exp (ρs * (n : ℝ) ^ 2 * Real.log 2) * Real.exp (-ρs * (n : ℝ) ^ 2) :=
          mul_le_mul h2 h1 hA (Real.exp_pos _).le
      _ = Real.exp (ρs * (n : ℝ) ^ 2 * Real.log 2 + -ρs * (n : ℝ) ^ 2) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-(3 / 10 * ρs * (n : ℝ) ^ 2)) := by
          apply Real.exp_le_exp.2
          have hpos : 0 ≤ ρs * (n : ℝ) ^ 2 := by positivity
          nlinarith
  have h4 : Real.exp (-(3 / 10 * ρs * (n : ℝ) ^ 2)) ≤ 120 / (3 / 10 * ρs * (n : ℝ) ^ 2) ^ 5 := by
    have h := Real.pow_div_factorial_le_exp _ hx.le 5
    rw [show ((Nat.factorial 5 : ℕ) : ℝ) = 120 by norm_num [Nat.factorial]] at h
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 120)] at h
    linarith
  have h5 : (120 : ℝ) / (3 / 10 * ρs * (n : ℝ) ^ 2) ^ 5 =
      120 / (3 / 10 * ρs) ^ 5 * (n : ℝ) ^ (-10 : ℤ) := by
    rw [zpow_neg, zpow_ofNat]
    field_simp
  linarith

/-! ## Random-sign model facts -/

lemma rs_mono {n : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (G H : RealMatrix n n → Prop)
    (hGH : ∀ E, G E → H E) : randomSignProb ρ G ≤ randomSignProb ρ H := by
  unfold randomSignProb
  refine Finset.sum_le_sum (fun Ω _ => Finset.sum_le_sum (fun P _ => ?_))
  have hw : 0 ≤ bernoulliObservationWeight ρ Ω * (1 / 2 : ℝ) ^ Ω.card :=
    mul_nonneg (bw_nonneg hρ0 hρ1 Ω) (by positivity)
  refine mul_le_mul_of_nonneg_left ?_ hw
  by_cases hG : G (signPattern Ω P)
  · simp [hG, hGH _ hG]
  · simp only [hG, if_false]
    split_ifs <;> norm_num

open scoped Classical in
/-- inner random-sign average over `P ⊆ Ω` -/
noncomputable def RSF {n : ℕ} (G : RealMatrix n n → Prop) (Ω : Finset (Fin n × Fin n)) : ℝ :=
  ∑ P ∈ Ω.powerset, (1 / 2 : ℝ) ^ Ω.card * (if G (signPattern Ω P) then 1 else 0)

open scoped Classical in
lemma rs_eq {n : ℕ} (ρ : ℝ) (G : RealMatrix n n → Prop) :
    randomSignProb ρ G = ∑ Ω, bernoulliObservationWeight ρ Ω * RSF G Ω := by
  unfold randomSignProb RSF
  refine Finset.sum_congr rfl (fun Ω _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  ring

lemma half_sum_one {n : ℕ} (Ω : Finset (Fin n × Fin n)) :
    ∑ _P ∈ Ω.powerset, (1 / 2 : ℝ) ^ Ω.card = 1 := by
  rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
  push_cast
  rw [← mul_pow]
  norm_num

lemma supp_signPattern {n : ℕ} (Ω P : Finset (Fin n × Fin n)) (hP : P ⊆ Ω) :
    supp (signPattern Ω P) = Ω := by
  ext ⟨i, j⟩
  simp only [supp, signPattern, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h1 : (i, j) ∈ P
  · simp [h1, hP h1]
  · by_cases h2 : (i, j) ∈ Ω <;> simp [h1, h2]

lemma signPattern_vals {n : ℕ} (Ω P : Finset (Fin n × Fin n)) (i j : Fin n) :
    signPattern Ω P i j = 1 ∨ signPattern Ω P i j = -1 ∨ signPattern Ω P i j = 0 := by
  simp only [signPattern]
  split_ifs <;> simp

lemma sign_absmul (s e : ℝ) (hs : s ≠ 0) (he : e = 1 ∨ e = -1 ∨ e = 0) :
    Real.sign (|s| * e) = e := by
  have hpos : 0 < |s| := abs_pos.2 hs
  rcases he with rfl | rfl | rfl
  · rw [mul_one, Real.sign_of_pos hpos]
  · rw [mul_neg_one, Real.sign_neg, Real.sign_of_pos hpos]
  · rw [mul_zero, Real.sign_zero]

lemma supp_absmul {n : ℕ} (S' E : RealMatrix n n) (hS' : ∀ i j, S' i j ≠ 0) :
    supp (fun i j => |S' i j| * E i j) = supp E := by
  ext ⟨i, j⟩
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h he; exact h (by rw [he, mul_zero])
  · intro h; exact mul_ne_zero (abs_pos.2 (hS' i j)).ne' h

lemma trimmed_absmul {n : ℕ} (S E : RealMatrix n n) :
    IsTrimmed (fun i j => |S i j| * E i j)
      (fun i j => |(if S i j = 0 then 1 else S i j)| * E i j) := by
  constructor
  · intro x hx
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have hS : S x.1 x.2 ≠ 0 := by intro h; apply hx; rw [h, abs_zero, zero_mul]
    rw [if_neg hS]; exact hx
  · intro i j h
    have hS : S i j ≠ 0 := by intro h'; apply h; simp [h']
    show |S i j| * E i j = |(if S i j = 0 then 1 else S i j)| * E i j
    rw [if_neg hS]

/-! ## The combined certificate -/

lemma cert {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (S' : RealMatrix n n)
    (hS' : ∀ i j, S' i j ≠ 0) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (Ω P : Finset (Fin n × Fin n)) (hP : P ⊆ Ω) (WLm : RealMatrix n n)
    (hWLT : tangentProjection SV WLm = 0)
    (h8a : MatrixCompletion.spectralNorm WLm < 1 / 4)
    (h8b : frobeniusNorm (samplingProjection Ω (signMatrix SV + WLm)) < lam / 4)
    (h8c : entrySupNorm (compProj Ω (signMatrix SV + WLm)) < lam / 4)
    (h9 : (∃ σ < 1 / 2, PTOpNormLe (supp (signPattern Ω P)) SV σ) ∧
      MatrixCompletion.spectralNorm (WS lam (supp (signPattern Ω P)) SV (signPattern Ω P)) < 1 / 4 ∧
      entrySupNorm (compProj (supp (signPattern Ω P))
        (WS lam (supp (signPattern Ω P)) SV (signPattern Ω P))) < lam / 4) :
    IsPCPExact lam L0 (fun i j => |S' i j| * signPattern Ω P i j) := by
  have hsuppE : supp (signPattern Ω P) = Ω := supp_signPattern Ω P hP
  rw [hsuppE] at h9
  obtain ⟨hPT, hWS1, hWS2⟩ := h9
  set E := signPattern Ω P with hEdef
  have hE : samplingProjection Ω E = E := by
    ext i j
    simp only [samplingProjection]
    split_ifs with h
    · rfl
    · simp only [hEdef, signPattern]
      have hnP : (i, j) ∉ P := fun h' => h (hP h')
      simp [hnP, h]
  set WSm := WS lam Ω SV E with hWSdef
  have hPWS := sampling_WS lam Ω SV E hE hPT
  have hS0supp : supp (fun i j => |S' i j| * E i j) = Ω := by
    rw [supp_absmul S' E hS', hsuppE]
  have hsgn : sgnMatrix (fun i j => |S' i j| * E i j) = E := by
    ext i j
    exact sign_absmul _ _ (hS' i j) (signPattern_vals Ω P i j)
  refine eq_2_4 lam L0 _ SV (WLm + WSm) hlam0 hlam1 ?_ ?_ ?_ ?_ ?_
  · rw [hS0supp]
    obtain ⟨σ, hσ, h⟩ := hPT
    exact PTOpNormLe_mono h hσ.le
  · rw [tangent_add, hWLT, hWSdef]
    unfold WS
    rw [tangent_smul, tangent_normal, smul_zero, zero_add]
  · calc MatrixCompletion.spectralNorm (WLm + WSm)
        ≤ MatrixCompletion.spectralNorm WLm + MatrixCompletion.spectralNorm WSm := spectral_add _ _
      _ < 1 / 2 := by linarith
  · rw [hS0supp, hsgn]
    have heq : samplingProjection Ω (signMatrix SV - lam • E + (WLm + WSm)) =
        samplingProjection Ω (signMatrix SV + WLm) := by
      ext i j
      have e1 := congrFun (congrFun hPWS i) j
      rw [← hWSdef] at e1
      simp only [samplingProjection, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
        Matrix.sub_apply] at e1 ⊢
      split_ifs at e1 ⊢ with h
      · rw [e1]; ring
      · rfl
    rw [heq]
    exact h8b.le
  · rw [hS0supp, ← add_assoc, compProj_add]
    calc entrySupNorm (compProj Ω (signMatrix SV + WLm) + compProj Ω WSm)
        ≤ entrySupNorm (compProj Ω (signMatrix SV + WLm)) + entrySupNorm (compProj Ω WSm) :=
          entrySup_add _ _
      _ < lam / 2 := by linarith

open scoped Classical in
lemma joint_bound {n : ℕ} (ρ q : ℝ) (j0 : ℕ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hρ : (1 - q) ^ j0 = ρ)
    (Ev8 : (Fin j0 → Finset (Fin n × Fin n)) → Prop) (Ev9 Succ : RealMatrix n n → Prop)
    (himp : ∀ Ωs P, P ⊆ golfOmega Ωs → Ev8 Ωs → Ev9 (signPattern (golfOmega Ωs) P) →
      Succ (signPattern (golfOmega Ωs) P)) :
    randomSignProb ρ Succ ≥ randomSignProb ρ Ev9 - (1 - golfingProb q j0 Ev8) := by
  set w : (Fin j0 → Finset (Fin n × Fin n)) → ℝ := fun Ωs => ∏ j, bernoulliObservationWeight q (Ωs j)
    with hw
  have hw0 : ∀ Ωs, 0 ≤ w Ωs := fun Ωs => Finset.prod_nonneg (fun j _ => bw_nonneg hq0 hq1 _)
  have hjoint : ∀ G : RealMatrix n n → Prop,
      randomSignProb ρ G = ∑ Ωs, w Ωs * RSF G (golfOmega Ωs) := by
    intro G
    rw [rs_eq, ← hρ]
    exact (golf_couple j0 q (RSF G)).symm
  have hwsum : ∑ Ωs, w Ωs = 1 := by
    have h := golf_couple (n := n) j0 q (fun _ => 1)
    simp only [mul_one] at h
    rw [h, bw_sum_one]
  have hpt : ∀ Ωs, RSF Succ (golfOmega Ωs) ≥
      RSF Ev9 (golfOmega Ωs) - (if Ev8 Ωs then 0 else 1) := by
    intro Ωs
    unfold RSF
    have hhalf := half_sum_one (golfOmega Ωs)
    have hrhs : ∑ P ∈ (golfOmega Ωs).powerset, (1 / 2 : ℝ) ^ (golfOmega Ωs).card *
          (if Ev9 (signPattern (golfOmega Ωs) P) then 1 else 0) - (if Ev8 Ωs then 0 else 1) =
        ∑ P ∈ (golfOmega Ωs).powerset, (1 / 2 : ℝ) ^ (golfOmega Ωs).card *
          ((if Ev9 (signPattern (golfOmega Ωs) P) then 1 else 0) - (if Ev8 Ωs then 0 else 1)) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hhalf, one_mul]
    rw [ge_iff_le, hrhs]
    refine Finset.sum_le_sum (fun P hP => mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [Finset.mem_powerset] at hP
    by_cases h8' : Ev8 Ωs
    · by_cases h9' : Ev9 (signPattern (golfOmega Ωs) P)
      · have hs := himp Ωs P hP h8' h9'
        simp [h8', h9', hs]
      · simp only [h8', h9', if_false, if_true]
        split_ifs <;> norm_num
    · simp only [h8', if_false]
      split_ifs <;> norm_num
  have hfail : ∑ Ωs, w Ωs * (if Ev8 Ωs then 0 else 1) = 1 - golfingProb q j0 Ev8 := by
    have hg8 : golfingProb q j0 Ev8 = ∑ Ωs, w Ωs * (if Ev8 Ωs then 1 else 0) := rfl
    have e : ∀ Ωs, w Ωs * (if Ev8 Ωs then (0 : ℝ) else 1) =
        w Ωs - w Ωs * (if Ev8 Ωs then 1 else 0) := by
      intro Ωs; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun Ωs _ => e Ωs), Finset.sum_sub_distrib, hwsum, hg8]
  rw [hjoint Succ, hjoint Ev9, ← hfail, ← Finset.sum_sub_distrib, ge_iff_le]
  refine Finset.sum_le_sum (fun Ωs _ => ?_)
  rw [← mul_sub]
  exact mul_le_mul_of_nonneg_left (hpt Ωs) (hw0 Ωs)

lemma key_rs {n r : ℕ} {L0 : RealMatrix n n} (SV : SVD L0 r) (S' : RealMatrix n n)
    (hS' : ∀ i j, S' i j ≠ 0) (ρ lam q : ℝ) (j0 : ℕ) (a8 a9 : ℝ)
    (hlam0 : 0 < lam) (hlam1 : lam < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hρ : (1 - q) ^ j0 = ρ)
    (h8 : golfingProb q j0 (fun Ωs =>
        MatrixCompletion.spectralNorm (WL SV q Ωs) < 1 / 4 ∧
        frobeniusNorm (samplingProjection (golfOmega Ωs) (signMatrix SV + WL SV q Ωs)) < lam / 4 ∧
        entrySupNorm (compProj (golfOmega Ωs) (signMatrix SV + WL SV q Ωs)) < lam / 4) ≥ 1 - a8)
    (h9 : randomSignProb ρ (fun E : RealMatrix n n =>
        (∃ σ < 1 / 2, PTOpNormLe (supp E) SV σ) ∧
        MatrixCompletion.spectralNorm (WS lam (supp E) SV E) < 1 / 4 ∧
        entrySupNorm (compProj (supp E) (WS lam (supp E) SV E)) < lam / 4) ≥ 1 - a9) :
    randomSignProb ρ (fun E => IsPCPExact lam L0 (fun i j => |S' i j| * E i j)) ≥
      1 - a8 - a9 := by
  have hj := joint_bound ρ q j0 hq0 hq1 hρ
    (fun Ωs =>
        MatrixCompletion.spectralNorm (WL SV q Ωs) < 1 / 4 ∧
        frobeniusNorm (samplingProjection (golfOmega Ωs) (signMatrix SV + WL SV q Ωs)) < lam / 4 ∧
        entrySupNorm (compProj (golfOmega Ωs) (signMatrix SV + WL SV q Ωs)) < lam / 4)
    (fun E : RealMatrix n n =>
        (∃ σ < 1 / 2, PTOpNormLe (supp E) SV σ) ∧
        MatrixCompletion.spectralNorm (WS lam (supp E) SV E) < 1 / 4 ∧
        entrySupNorm (compProj (supp E) (WS lam (supp E) SV E)) < lam / 4)
    (fun E => IsPCPExact lam L0 (fun i j => |S' i j| * E i j))
    (fun Ωs P hP h8' h9' => by
      obtain ⟨h8a, h8b, h8c⟩ := h8'
      exact cert SV S' hS' lam hlam0 hlam1 (golfOmega Ωs) P hP (WL SV q Ωs)
        (by unfold WL; exact tangent_normal SV _) h8a h8b h8c h9')
  linarith

end RPCA429

open RPCA429 RobustPCA.Recovery in
theorem solution :
    ∃ c ρr ρs : ℝ, 0 < c ∧ 0 < ρr ∧ 0 < ρs ∧
      ∀ (n r m : ℕ) (L0 S : RealMatrix n n) (SV : SVD L0 r) (μ : ℝ),
        0 < n → Incoherent SV μ →
        (r : ℝ) * μ * Real.log n ^ 2 ≤ ρr * n →
        (m : ℝ) ≤ ρs * (n : ℝ) ^ 2 →
        fixedCardinalityEventProb m
            (fun Ω => IsPCPExact (1 / Real.sqrt n) L0 (samplingProjection Ω S)) ≥
          1 - c * (n : ℝ) ^ (-10 : ℤ) := by
  obtain ⟨ρs8, ρr8, c8, hρs8, hρr8, hc8, H8⟩ := lemma_2_8
  obtain ⟨ρs9, ρr9, c9, hρs9, hρr9, hc9, H9⟩ := lemma_2_9
  have hρs_pos : 0 < min (1 / 8 : ℝ) (min ρs8 ρs9 / 4) :=
    lt_min (by norm_num) (by have := lt_min hρs8 hρs9; positivity)
  refine ⟨1 + c8 + c9 + 120 / (3 / 10 * min (1 / 8 : ℝ) (min ρs8 ρs9 / 4)) ^ 5,
    min ρr8 ρr9, min (1 / 8 : ℝ) (min ρs8 ρs9 / 4), by positivity, lt_min hρr8 hρr9, hρs_pos, ?_⟩
  intro n r m L0 S SV μ hn hinc hrank hm
  set ρs := min (1 / 8 : ℝ) (min ρs8 ρs9 / 4) with hρsdef
  have hρs18 : ρs ≤ 1 / 8 := min_le_left _ _
  have hρs4 : 4 * ρs ≤ min ρs8 ρs9 := by
    have := min_le_right (1 / 8 : ℝ) (min ρs8 ρs9 / 4); linarith
  have hρs8' : 4 * ρs ≤ ρs8 := hρs4.trans (min_le_left _ _)
  have hρs9' : 4 * ρs ≤ ρs9 := hρs4.trans (min_le_right _ _)
  set C := 120 / (3 / 10 * ρs) ^ 5 with hCdef
  have hC : 0 < C := by positivity
  have hnpow : 0 ≤ (n : ℝ) ^ (-10 : ℤ) := by positivity
  have hFnn : 0 ≤ fixedCardinalityEventProb m
      (fun Ω => IsPCPExact (1 / Real.sqrt n) L0 (samplingProjection Ω S)) := by
    simp only [fixedCardinalityEventProb]
    positivity
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
  · simp only [Nat.cast_one, one_zpow, mul_one]
    linarith
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hsqrt : 1 < Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hlam0 : 0 < 1 / Real.sqrt n := by positivity
  have hlam1 : 1 / Real.sqrt n < 1 := by rw [div_lt_one (by linarith)]; exact hsqrt
  have hm' : m ≤ n * n := by
    have h1 : (m : ℝ) ≤ ((n * n : ℕ) : ℝ) := by
      push_cast
      have : 0 ≤ (n : ℝ) ^ 2 := by positivity
      nlinarith
    exact_mod_cast h1
  -- transfer, tail and derandomization
  have hT := sec_7_1_transfer (1 / Real.sqrt n) L0 S m (2 * ρs) hlam0.le hm' (by positivity)
    (by linarith)
  have htail := (ber_tail (n := n) m (2 * ρs) (by positivity) (by linarith)).trans
    (tail_poly n m ρs hρs_pos (by linarith) hn hm)
  have hD := theorem_2_3 (1 / Real.sqrt n) (2 * ρs) L0 S hlam0.le (by positivity) (by linarith)
  -- replace zero entries of S by 1 (elimination)
  set S' : RealMatrix n n := fun i j => if S i j = 0 then 1 else S i j with hS'def
  have hS' : ∀ i j, S' i j ≠ 0 := by
    intro i j
    simp only [hS'def]
    split_ifs with h
    · norm_num
    · exact h
  have hmono := rs_mono (ρ := 2 * (2 * ρs)) (by positivity) (by linarith)
    (fun E => IsPCPExact (1 / Real.sqrt n) L0 (fun i j => |S' i j| * E i j))
    (fun E => IsPCPExact (1 / Real.sqrt n) L0 (fun i j => |S i j| * E i j))
    (fun E h => theorem_2_2 _ _ _ _ hlam0.le h (trimmed_absmul S E))
  -- golfing parameters
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hj0 : 1 ≤ 2 * ⌈Real.log n⌉₊ := by
    have : 0 < ⌈Real.log n⌉₊ := Nat.ceil_pos.2 hlog
    omega
  have hj0R : (0 : ℝ) < ((2 * ⌈Real.log n⌉₊ : ℕ) : ℝ) := by exact_mod_cast hj0
  have hρ0 : (0 : ℝ) ≤ 2 * (2 * ρs) := by positivity
  have hρ1 : 2 * (2 * ρs) ≤ 1 := by linarith
  have hr0 : 0 ≤ (2 * (2 * ρs)) ^ ((1 : ℝ) / ((2 * ⌈Real.log n⌉₊ : ℕ) : ℝ)) :=
    Real.rpow_nonneg hρ0 _
  have hr1 : (2 * (2 * ρs)) ^ ((1 : ℝ) / ((2 * ⌈Real.log n⌉₊ : ℕ) : ℝ)) ≤ 1 :=
    Real.rpow_le_one hρ0 hρ1 (by positivity)
  have hρeq : (1 - (1 - (2 * (2 * ρs)) ^ ((1 : ℝ) / ((2 * ⌈Real.log n⌉₊ : ℕ) : ℝ)))) ^
      (2 * ⌈Real.log n⌉₊) = 2 * (2 * ρs) := by
    rw [sub_sub_cancel, ← Real.rpow_natCast, ← Real.rpow_mul hρ0,
      one_div_mul_cancel hj0R.ne', Real.rpow_one]
  have hrank8 : (r : ℝ) * μ * Real.log n ^ 2 ≤ ρr8 * n :=
    hrank.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
  have hrank9 : (r : ℝ) * μ * Real.log n ^ 2 ≤ ρr9 * n :=
    hrank.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _))
  have h8 := H8 n r L0 SV μ (2 * (2 * ρs)) hn hinc hrank8 (by positivity) (by linarith)
  have h9 := H9 n r L0 SV μ (2 * (2 * ρs)) hn hinc hrank9 (by positivity) (by linarith)
  dsimp only at h8 h9
  have hkey := key_rs SV S' hS' (2 * (2 * ρs)) (1 / Real.sqrt n)
    (1 - (2 * (2 * ρs)) ^ ((1 : ℝ) / ((2 * ⌈Real.log n⌉₊ : ℕ) : ℝ))) (2 * ⌈Real.log n⌉₊)
    (c8 * (n : ℝ) ^ (-10 : ℤ)) (c9 * (n : ℝ) ^ (-10 : ℤ)) hlam0 hlam1
    (by linarith) (by linarith) hρeq h8 h9
  have hc8n : 0 ≤ c8 * (n : ℝ) ^ (-10 : ℤ) := by positivity
  nlinarith
