-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P40.optimumEncodingSDP
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T15:48:58.980774+00:00
-- url     : https://prove2.me/submissions/2ac1b04c-f940-405c-b5c2-f758e295b4e0

import Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P40_choiChannelCorrespondence
import Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P40_entanglementFidelityKrausChoi

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P40

open scoped ComplexConjugate ComplexOrder Matrix

open QAlgorithms.Papers.Independent.Information100.P34 (dyad)

open Matrix

lemma x8_tr_dyad {ι : Type*} [Fintype ι] (a b : EuclideanSpace ℂ ι) :
    (dyad a a * dyad b b).trace =
      ((Complex.normSq (∑ p, conj (b p) * a p) : ℝ) : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [Matrix.trace, Matrix.mul_apply, dyad, Matrix.diag, map_sum, map_mul,
    Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

lemma x8_ket_inner {h k : ℕ} (rho : Matrix (Fin h) (Fin h) ℂ) (hr : rhoᴴ = rho)
    (M : Matrix (Fin h) (Fin k) ℂ) (K : Matrix (Fin k) (Fin h) ℂ) :
    ∑ p, conj (operatorKet (Mᴴ * rho) p) * operatorKet K p = (rho * (M * K)).trace := by
  have hr' : ∀ y u, conj (rho y u) = rho u y := by
    intro y u
    have := congrFun (congrFun hr u) y
    simpa [Matrix.conjTranspose_apply] using this
  simp only [operatorKet, Fintype.sum_prod_type, PiLp.toLp_apply]
  have e1 : ∀ x u, conj ((Mᴴ * rho) x u) = ∑ y, M y x * rho u y := by
    intro x u
    rw [Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Matrix.conjTranspose_apply, map_mul, hr']
    simp
  have e2 : (rho * (M * K)).trace = ∑ u, ∑ y, ∑ x, rho u y * (M y x * K x u) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
  simp only [e1, e2, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

lemma x8_trace_obj {h k M0 m n : ℕ} (rho : Matrix (Fin h) (Fin h) ℂ) (hr : rhoᴴ = rho)
    (K : Fin M0 → Matrix (Fin k) (Fin h) ℂ)
    (E : Fin m → Matrix (Fin k) (Fin k) ℂ) (D : Fin n → Matrix (Fin h) (Fin k) ℂ) :
    (krausChoi K * encodingCoefficient rho E D).trace =
      ∑ i, ∑ j, ∑ l, ((Complex.normSq ((rho * (D i * E j * K l)).trace) : ℝ) : ℂ) := by
  simp only [krausChoi, encodingCoefficient, Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum,
    x8_tr_dyad, x8_ket_inner rho hr]


/-- the composed Kraus family on a `Fin` index -/
def x8B {h k m n M0 : ℕ} (E : Fin m → Matrix (Fin k) (Fin k) ℂ)
    (D : Fin n → Matrix (Fin h) (Fin k) ℂ) (K : Fin M0 → Matrix (Fin k) (Fin h) ℂ) :
    Fin (Fintype.card (Fin n × Fin m × Fin M0)) → Matrix (Fin h) (Fin h) ℂ :=
  fun t => D ((Fintype.equivFin _).symm t).1 * E ((Fintype.equivFin _).symm t).2.1 *
    K ((Fintype.equivFin _).symm t).2.2

lemma x8B_sum {h k m n M0 : ℕ} {β : Type*} [AddCommMonoid β] (E : Fin m → Matrix (Fin k) (Fin k) ℂ)
    (D : Fin n → Matrix (Fin h) (Fin k) ℂ) (K : Fin M0 → Matrix (Fin k) (Fin h) ℂ)
    (f : Matrix (Fin h) (Fin h) ℂ → β) :
    ∑ t, f (x8B E D K t) = ∑ i, ∑ j, ∑ l, f (D i * E j * K l) := by
  rw [Fintype.sum_equiv (Fintype.equivFin _).symm (fun t => f (x8B E D K t))
    (fun x => f (D x.1 * E x.2.1 * K x.2.2)) (fun t => rfl)]
  simp only [Fintype.sum_prod_type]

lemma x8B_apply {h k m n M0 : ℕ} (E : Fin m → Matrix (Fin k) (Fin k) ℂ)
    (D : Fin n → Matrix (Fin h) (Fin k) ℂ) (K : Fin M0 → Matrix (Fin k) (Fin h) ℂ) :
    krausApply D ∘ krausApply E ∘ krausApply K = krausApply (x8B E D K) := by
  funext X
  simp only [Function.comp_apply, krausApply]
  rw [x8B_sum E D K (fun B => B * X * Bᴴ)]
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma x8B_kraus {h k m n M0 : ℕ} (E : Fin m → Matrix (Fin k) (Fin k) ℂ)
    (D : Fin n → Matrix (Fin h) (Fin k) ℂ) (K : Fin M0 → Matrix (Fin k) (Fin h) ℂ)
    (hE : IsKrausFamily E) (hD : IsKrausFamily D) (hK : IsKrausFamily K) :
    IsKrausFamily (x8B E D K) := by
  unfold IsKrausFamily at *
  rw [x8B_sum E D K (fun B => Bᴴ * B)]
  have : ∀ j l, ∑ i, (D i * E j * K l)ᴴ * (D i * E j * K l) = (K l)ᴴ * (E j)ᴴ * E j * K l := by
    intro j l
    rw [show ∑ i, (D i * E j * K l)ᴴ * (D i * E j * K l) =
        (K l)ᴴ * (E j)ᴴ * (∑ i, (D i)ᴴ * D i) * E j * K l by
      simp only [Matrix.mul_sum, Matrix.sum_mul]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc], hD, Matrix.mul_one]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun j _ => Finset.sum_comm, Finset.sum_comm]
  simp only [this]
  rw [← hK]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show ∑ j, (K l)ᴴ * (E j)ᴴ * E j * K l = (K l)ᴴ * (∑ j, (E j)ᴴ * E j) * K l by
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc], hE, Matrix.mul_one]

lemma x8_fid {h k a m n M0 : ℕ} (hh : 0 < h)
    (rho : Matrix (Fin h) (Fin h) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin h)) (hpsi : IsPurification rho psi)
    (E : Fin m → Matrix (Fin k) (Fin k) ℂ) (hE : IsKrausFamily E)
    (D : Fin n → Matrix (Fin h) (Fin k) ℂ) (hD : IsKrausFamily D)
    (K : Fin M0 → Matrix (Fin k) (Fin h) ℂ) (hK : IsKrausFamily K) :
    purificationFidelity psi (krausApply D ∘ krausApply E ∘ krausApply K) =
      ∑ i, ∑ j, ∑ l, Complex.normSq ((rho * (D i * E j * K l)).trace) := by
  rw [x8B_apply, (entanglementFidelityKrausChoi hh rho hrho psi hpsi _
    (x8B_kraus E D K hE hD hK)).1]
  exact x8B_sum E D K (fun B => Complex.normSq ((rho * B).trace))


lemma x8_bound {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ) (hX : ChoiFeasible X) (p q : Fin k × Fin h) :
    ‖X p q‖ ≤ h := by
  obtain ⟨N, A, rfl⟩ :=
    ((choiChannelCorrespondence hh hk (fun _ : Fin 0 => (0 : Matrix (Fin k) (Fin h) ℂ))).2.2.2.2.1
      X).mp hX.1
  set S : Fin k × Fin h → ℝ := fun p => ∑ j, ‖A j p.1 p.2‖ ^ 2 with hS
  have hent : ∀ p q, krausChoi A p q = ∑ j, A j p.1 p.2 * conj (A j q.1 q.2) := by
    intro p q
    simp [krausChoi, dyad, operatorKet, Matrix.sum_apply]
  have hsum : ∑ p, S p = h := by
    have h1 : ∀ u, ∑ x, krausChoi A (x, u) (x, u) = 1 := by
      intro u
      have := congrFun (congrFun hX.2 u) u
      simpa [traceLeft] using this
    have h2 : ∑ p, ((S p : ℝ) : ℂ) = ∑ p, krausChoi A p p := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hent, hS]
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    have h3 : ∑ p, krausChoi A p p = h := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp [h1]
    have : ((∑ p, S p : ℝ) : ℂ) = (h : ℂ) := by push_cast; rw [h2, h3]
    exact_mod_cast this
  have hSn : ∀ p, 0 ≤ S p := fun p => Finset.sum_nonneg fun j _ => by positivity
  have hSle : ∀ p, S p ≤ h := by
    intro p
    rw [← hsum]
    exact Finset.single_le_sum (fun p _ => hSn p) (Finset.mem_univ p)
  rw [hent]
  calc ‖∑ j, A j p.1 p.2 * conj (A j q.1 q.2)‖
      ≤ ∑ j, ‖A j p.1 p.2 * conj (A j q.1 q.2)‖ := norm_sum_le _ _
    _ ≤ ∑ j, (‖A j p.1 p.2‖ ^ 2 + ‖A j q.1 q.2‖ ^ 2) / 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, Complex.norm_conj]
        nlinarith [sq_nonneg (‖A j p.1 p.2‖ - ‖A j q.1 q.2‖)]
    _ = (S p + S q) / 2 := by rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ h := by linarith [hSle p, hSle q]

lemma x8_closed {h k : ℕ} :
    IsClosed {X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ | ChoiFeasible X} := by
  have e : {X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ | ChoiFeasible X} =
      {X | Xᴴ = X} ∩ (⋂ x : Fin k × Fin h → ℂ, {X | 0 ≤ star x ⬝ᵥ X *ᵥ x}) ∩
        {X | traceLeft X = 1} := by
    ext X
    simp only [ChoiFeasible, Matrix.posSemidef_iff_dotProduct_mulVec, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_iInter, Matrix.IsHermitian, and_assoc]
  rw [e]
  refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
  · exact isClosed_eq (by fun_prop) continuous_id
  · refine isClosed_iInter fun x => ?_
    exact isClosed_le continuous_const (by fun_prop)
  · refine isClosed_eq ?_ continuous_const
    unfold traceLeft
    fun_prop

lemma x8_compact {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    IsCompact {X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ | ChoiFeasible X} := by
  have hK : IsCompact (Set.univ.pi fun _ : Fin k × Fin h =>
      Set.univ.pi fun _ : Fin k × Fin h => Metric.closedBall (0 : ℂ) h) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hK.of_isClosed_subset x8_closed ?_
  intro X hX
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  exact fun p q => x8_bound hh hk X hX p q


lemma x8_part1 {h k a m n : ℕ} (hh : 0 < h) (hk : 0 < k)
    (rho : Matrix (Fin h) (Fin h) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin h)) (hpsi : IsPurification rho psi)
    (E : Fin m → Matrix (Fin k) (Fin k) ℂ) (hE : IsKrausFamily E)
    (D : Fin n → Matrix (Fin h) (Fin k) ℂ) (hD : IsKrausFamily D)
    (V : Superop (Fin h) (Fin k)) (hV : IsChannel V) :
    ChoiFeasible (outputFirstChoi V) ∧
      purificationFidelity psi (krausApply D ∘ krausApply E ∘ V) =
        (outputFirstChoi V * encodingCoefficient rho E D).trace.re := by
  obtain ⟨M0, K, hK, hVK⟩ := hV
  have hVf : V = krausApply K := funext hVK
  have C := choiChannelCorrespondence hh hk K
  refine ⟨?_, ?_⟩
  · rw [C.2.2.2.2.2.1, C.2.2.2.2.2.2.2 V ⟨M0, K, hK, hVK⟩]
    exact ⟨M0, K, hK, hVK⟩
  · have hr : rhoᴴ = rho := hrho.1.1
    rw [hVf, x8_fid hh rho hrho psi hpsi E hE D hD K hK, C.2.1, x8_trace_obj rho hr]
    simp only [Complex.re_sum, Complex.ofReal_re]

lemma x8_main {h k a m n : ℕ} (hh : 0 < h) (hk : 0 < k) (hspread : h < k)
    (rho : Matrix (Fin h) (Fin h) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin h)) (hpsi : IsPurification rho psi)
    (E : Fin m → Matrix (Fin k) (Fin k) ℂ) (hE : IsKrausFamily E)
    (D : Fin n → Matrix (Fin h) (Fin k) ℂ) (hD : IsKrausFamily D) :
    (∀ V : Superop (Fin h) (Fin k), IsChannel V →
      ChoiFeasible (outputFirstChoi V) ∧
      purificationFidelity psi (krausApply D ∘ krausApply E ∘ V) =
        (outputFirstChoi V * encodingCoefficient rho E D).trace.re) ∧
    (∀ X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ, ChoiFeasible X →
      ∃ V : Superop (Fin h) (Fin k), IsChannel V ∧ outputFirstChoi V = X) ∧
    ∃ (V : Superop (Fin h) (Fin k))
      (X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ),
      IsChannel V ∧ outputFirstChoi V = X ∧ ChoiFeasible X ∧
      purificationFidelity psi (krausApply D ∘ krausApply E ∘ V) =
        (X * encodingCoefficient rho E D).trace.re ∧
      (∀ Y, ChoiFeasible Y → (Y * encodingCoefficient rho E D).trace.re ≤
        (X * encodingCoefficient rho E D).trace.re) ∧
      (∀ W : Superop (Fin h) (Fin k), IsChannel W →
        purificationFidelity psi (krausApply D ∘ krausApply E ∘ W) ≤
          purificationFidelity psi (krausApply D ∘ krausApply E ∘ V)) := by
  have C := choiChannelCorrespondence hh hk (fun _ : Fin 0 => (0 : Matrix (Fin k) (Fin h) ℂ))
  have P1 := x8_part1 hh hk rho hrho psi hpsi E hE D hD
  have P2 : ∀ X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ, ChoiFeasible X →
      ∃ V : Superop (Fin h) (Fin k), IsChannel V ∧ outputFirstChoi V = X :=
    fun X hX => ⟨fromOutputFirstChoi X, (C.2.2.2.2.2.1 X).mp hX, C.2.2.2.2.2.2.1 X⟩
  refine ⟨P1, P2, ?_⟩
  have hne : ({X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ | ChoiFeasible X}).Nonempty := by
    refine ⟨((k : ℂ)⁻¹) • 1, ?_, ?_⟩
    · exact Matrix.PosSemidef.one.smul (by
        have : (0 : ℝ) ≤ (k : ℝ)⁻¹ := by positivity
        have h2 := Complex.zero_le_real.mpr this
        simpa using h2)
    · ext u v
      by_cases huv : u = v
      · subst huv
        simp [traceLeft, Matrix.one_apply]
        field_simp
      · simp [traceLeft, Matrix.one_apply, huv]
  obtain ⟨X, hX, hmax⟩ := (x8_compact hh hk).exists_isMaxOn hne
    (Continuous.continuousOn (f := fun Y : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ =>
      (Y * encodingCoefficient rho E D).trace.re) (by fun_prop))
  obtain ⟨V, hV, hVX⟩ := P2 X hX
  refine ⟨V, X, hV, hVX, hX, ?_, ?_, ?_⟩
  · rw [(P1 V hV).2, hVX]
  · intro Y hY
    exact hmax hY
  · intro W hW
    rw [(P1 V hV).2, (P1 W hW).2, hVX]
    exact hmax (P1 W hW).1

end QAlgorithms.Papers.Independent.Dependency50.P40

open QAlgorithms.Papers.Independent.Dependency50.P40 in
theorem solution {h k a m n : ℕ} (hh : 0 < h) (hk : 0 < k) (hspread : h < k)
    (rho : Matrix (Fin h) (Fin h) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin h)) (hpsi : IsPurification rho psi)
    (E : Fin m → Matrix (Fin k) (Fin k) ℂ) (hE : QAlgorithms.IsKrausFamily E)
    (D : Fin n → Matrix (Fin h) (Fin k) ℂ) (hD : QAlgorithms.IsKrausFamily D) :
    (∀ V : QAlgorithms.Superop (Fin h) (Fin k), QAlgorithms.IsChannel V →
      ChoiFeasible (outputFirstChoi V) ∧
      purificationFidelity psi (QAlgorithms.krausApply D ∘ QAlgorithms.krausApply E ∘ V) =
        (outputFirstChoi V * encodingCoefficient rho E D).trace.re) ∧
    (∀ X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ, ChoiFeasible X →
      ∃ V : QAlgorithms.Superop (Fin h) (Fin k), QAlgorithms.IsChannel V ∧ outputFirstChoi V = X) ∧
    ∃ (V : QAlgorithms.Superop (Fin h) (Fin k))
      (X : Matrix (Fin k × Fin h) (Fin k × Fin h) ℂ),
      QAlgorithms.IsChannel V ∧ outputFirstChoi V = X ∧ ChoiFeasible X ∧
      purificationFidelity psi (QAlgorithms.krausApply D ∘ QAlgorithms.krausApply E ∘ V) =
        (X * encodingCoefficient rho E D).trace.re ∧
      (∀ Y, ChoiFeasible Y → (Y * encodingCoefficient rho E D).trace.re ≤
        (X * encodingCoefficient rho E D).trace.re) ∧
      (∀ W : QAlgorithms.Superop (Fin h) (Fin k), QAlgorithms.IsChannel W →
        purificationFidelity psi (QAlgorithms.krausApply D ∘ QAlgorithms.krausApply E ∘ W) ≤
          purificationFidelity psi (QAlgorithms.krausApply D ∘ QAlgorithms.krausApply E ∘ V)) :=
  x8_main hh hk hspread rho hrho psi hpsi E hE D hD
