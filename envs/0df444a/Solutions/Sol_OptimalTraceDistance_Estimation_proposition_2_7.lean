-- Prove2me | solution 1 for OptimalTraceDistance.Estimation.proposition_2_7
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T05:52:18.454324+00:00
-- url     : https://prove2.me/submissions/26e7d8b2-2dc9-460e-b2ed-1652251019c2

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder MatrixOrder
noncomputable section

namespace OTDProp27
open Matrix OptimalTraceDistance.Estimation

variable {d n : ℕ}

lemma kron_mul {ι : Type*} [Fintype ι] {r : ℕ} (A B : Fin r → Matrix ι ι ℂ) :
    OptimalSpectrum.Entangled.kronFamily (fun j => A j * B j) =
      OptimalSpectrum.Entangled.kronFamily A * OptimalSpectrum.Entangled.kronFamily B := by
  ext x y
  simp only [OptimalSpectrum.Entangled.kronFamily, mul_apply, Matrix.of_apply]
  have := Fintype.prod_sum (fun (j : Fin r) (c : ι) => A j (x j) c * B j c (y j))
  rw [this]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.prod_mul_distrib]

lemma kron_conj {ι : Type*} [Fintype ι] {r : ℕ} (A : Fin r → Matrix ι ι ℂ) :
    (OptimalSpectrum.Entangled.kronFamily A)ᴴ =
      OptimalSpectrum.Entangled.kronFamily (fun j => (A j)ᴴ) := by
  ext x y
  simp [OptimalSpectrum.Entangled.kronFamily, conjTranspose_apply, star_prod]

lemma powerState_psd {ι : Type*} [Fintype ι] [DecidableEq ι] {τ : Matrix ι ι ℂ} (hτ : τ.PosSemidef)
    (n : ℕ) : (powerState τ n).PosSemidef := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hτ.nonneg
  have : powerState τ n = (OptimalSpectrum.Entangled.kronFamily (fun _ : Fin n => B))ᴴ *
      OptimalSpectrum.Entangled.kronFamily (fun _ : Fin n => B) := by
    rw [kron_conj, ← kron_mul]
    simp only [powerState, tensor, hB, Matrix.star_eq_conjTranspose]
  rw [this]; exact posSemidef_conjTranspose_mul_self _

lemma labelled_psd {d : ℕ} {ρ σ : Mat d} (hρ : Density ρ) (hσ : Density σ) :
    (labelledState ρ σ).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
  · ext ⟨b, i⟩ ⟨b', j⟩
    simp only [labelledState, conjTranspose_apply]
    by_cases h : b' = b
    · subst h
      simp only [if_true]
      cases b'
      · simp only [Bool.false_eq_true, if_false, star_mul', star_inv₀, star_ofNat]
        rw [show star (ρ j i) = ρ i j from by
          have := congrFun (congrFun hρ.1.1 i) j; simpa [conjTranspose_apply] using this]
      · simp only [if_true, star_mul', star_inv₀, star_ofNat]
        rw [show star (σ j i) = σ i j from by
          have := congrFun (congrFun hσ.1.1 i) j; simpa [conjTranspose_apply] using this]
    · rw [if_neg h, if_neg (Ne.symm h)]; simp
  · set u : Fin d → ℂ := fun i => x (false, i)
    set w : Fin d → ℂ := fun i => x (true, i)
    have e : star x ⬝ᵥ (labelledState ρ σ *ᵥ x) =
        (2:ℂ)⁻¹ * (star u ⬝ᵥ (ρ *ᵥ u)) + (2:ℂ)⁻¹ * (star w ⬝ᵥ (σ *ᵥ w)) := by
      simp only [dotProduct, mulVec, labelledState, Fintype.sum_prod_type, Fintype.sum_bool,
        Pi.star_apply, u, w]
      simp [Finset.mul_sum, Finset.sum_add_distrib, mul_comm, mul_left_comm, mul_assoc]
      ring_nf
    rw [e]
    have h2 : (0:ℂ) ≤ (2:ℂ)⁻¹ := by
      rw [show (2:ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by push_cast; rfl]; exact_mod_cast (by norm_num : (0:ℝ) ≤ 2⁻¹)
    exact add_nonneg (mul_nonneg h2 (hρ.1.dotProduct_mulVec_nonneg u))
      (mul_nonneg h2 (hσ.1.dotProduct_mulVec_nonneg w))


lemma herm_smul_real' {ι : Type*} [Fintype ι] (c : ℝ) {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    ((c : ℂ) • A).IsHermitian := by
  unfold IsHermitian at hA ⊢; rw [conjTranspose_smul, hA]; simp [Complex.conj_ofReal]

lemma herm_finsum {ι κ : Type*} [Fintype ι] (S : Finset κ) (A : κ → Matrix ι ι ℂ)
    (h : ∀ k ∈ S, (A k).IsHermitian) : (∑ k ∈ S, A k).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_sum]
  exact Finset.sum_congr rfl (fun k hk => h k hk)

lemma embed_herm {ι : Type*} [Fintype ι] [DecidableEq ι] {k n : ℕ} (e : Fin k ↪ Fin n)
    {H : Matrix (Fin k → ι) (Fin k → ι) ℂ} (hH : H.IsHermitian) : (embed e H).IsHermitian := by
  ext x y
  simp only [conjTranspose_apply, embed]
  have hc : (∀ i, i ∉ Set.range e → y i = x i) ↔ (∀ i, i ∉ Set.range e → x i = y i) :=
    ⟨fun h i hi => (h i hi).symm, fun h i hi => (h i hi).symm⟩
  by_cases h : ∀ i, i ∉ Set.range e → x i = y i
  · rw [if_pos (hc.mpr h), if_pos h]
    have := congrFun (congrFun hH (x ∘ e)) (y ∘ e)
    simpa [conjTranspose_apply] using this
  · rw [if_neg (fun h' => h (hc.mp h')), if_neg h, star_zero]

lemma uStat_herm {ι : Type*} [Fintype ι] [DecidableEq ι] (n k : ℕ)
    {H : Matrix (Fin k → ι) (Fin k → ι) ℂ} (hH : H.IsHermitian) : (uStatistic n k H).IsHermitian := by
  unfold uStatistic
  have hs : (∑ e : Fin k ↪ Fin n, embed e H).IsHermitian :=
    herm_finsum _ _ (fun e _ => embed_herm e hH)
  unfold IsHermitian at hs ⊢
  rw [conjTranspose_smul, hs]; congr 1; simp

lemma hermPart_herm {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : (hermPart A).IsHermitian := by
  unfold hermPart IsHermitian
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]; simp

lemma obs_herm (g : TraceExpression d) (n : ℕ) : (observable g n).IsHermitian := by
  unfold observable
  refine IsHermitian.add ?_ (herm_finsum _ _ (fun k _ => uStat_herm n k (hermPart_herm _)))
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact herm_smul_real' _ isHermitian_one


lemma trace_powerState {ι : Type*} [Fintype ι] (τ : Matrix ι ι ℂ) (n : ℕ) :
    (powerState τ n).trace = τ.trace ^ n := by
  simp only [powerState, tensor, OptimalSpectrum.Entangled.kronFamily, Matrix.trace, Matrix.diag,
    Matrix.of_apply]
  have h := Fintype.prod_sum (fun (_ : Fin n) (i : ι) => τ i i)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [h]

lemma trace_labelled {d : ℕ} {ρ σ : Mat d} (hρ : Density ρ) (hσ : Density σ) :
    (labelledState ρ σ).trace = 1 := by
  simp only [Matrix.trace, Matrix.diag, labelledState, if_true, Fintype.sum_prod_type,
    Fintype.sum_bool, if_false, Bool.false_eq_true]
  have h1 := hρ.2; have h2 := hσ.2
  simp only [Matrix.trace, Matrix.diag] at h1 h2
  rw [← Finset.mul_sum, ← Finset.mul_sum, h1, h2]; norm_num




abbrev IReg (d n : ℕ) := (Fin n → Fin d) × (Fin n → Fin d)
abbrev JReg (d n : ℕ) := Fin n → Bool × Fin d

def sel (b : Fin n → Bool) (p : IReg d n) : JReg d n :=
  fun i => (b i, if b i then p.2 i else p.1 i)
def rest (b : Fin n → Bool) (p : IReg d n) : Fin n → Fin d :=
  fun i => if b i then p.1 i else p.2 i
def unsel (b : Fin n → Bool) (j : JReg d n) (r : Fin n → Fin d) : IReg d n :=
  (fun i => if b i then r i else (j i).2, fun i => if b i then (j i).2 else r i)

def K (b : Fin n → Bool) (r : Fin n → Fin d) : Matrix (JReg d n) (IReg d n) ℂ :=
  fun j p => if j = sel b p ∧ rest b p = r then 1 else 0

def chanAdj (A : Matrix (JReg d n) (JReg d n) ℂ) : Matrix (IReg d n) (IReg d n) ℂ :=
  ((2:ℂ)^n)⁻¹ • ∑ b : Fin n → Bool, ∑ r : Fin n → Fin d, (K b r)ᴴ * A * K b r

lemma sel_rest_inj (b : Fin n → Bool) (p p' : IReg d n) :
    (sel b p = sel b p' ∧ rest b p = rest b p') ↔ p = p' := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨x, y⟩ := p; obtain ⟨x', y'⟩ := p'
    have hx : x = x' := by
      funext i
      have a1 := congrFun h1 i; have a2 := congrFun h2 i
      simp only [sel, rest, Prod.mk.injEq] at a1 a2
      by_cases hb : b i <;> simp [hb] at a1 a2 <;> assumption
    have hy : y = y' := by
      funext i
      have a1 := congrFun h1 i; have a2 := congrFun h2 i
      simp only [sel, rest, Prod.mk.injEq] at a1 a2
      by_cases hb : b i <;> simp [hb] at a1 a2 <;> assumption
    rw [hx, hy]
  · rintro rfl; exact ⟨rfl, rfl⟩

lemma K_conj (b : Fin n → Bool) (r : Fin n → Fin d) (j : JReg d n) (p : IReg d n) :
    star (K b r j p) = K b r j p := by
  unfold K; split_ifs <;> simp

lemma KK_one (b : Fin n → Bool) :
    ∑ r : Fin n → Fin d, (K b r)ᴴ * (1 : Matrix (JReg d n) (JReg d n) ℂ) * K b r = 1 := by
  ext p p'
  simp only [Matrix.mul_one, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    K_conj]
  have : ∀ r, ∑ j, K b r j p * K b r j p' = if rest b p = r ∧ p = p' then 1 else 0 := by
    intro r
    rw [Finset.sum_eq_single (sel b p)]
    · unfold K
      by_cases h : p = p'
      · subst h; by_cases hr : rest b p = r <;> simp [hr]
      · have : ¬ (sel b p = sel b p' ∧ rest b p' = r ∧ rest b p = r) := by
          rintro ⟨h1, h2, h3⟩
          exact h ((sel_rest_inj b p p').1 ⟨h1, h3.trans h2.symm⟩)
        simp only [h, and_false, if_false]
        split_ifs with h1 h2 <;> simp_all
    · intro j _ hj; unfold K; simp [Ne.symm hj, hj]
    · simp
  simp only [this]
  by_cases h : p = p'
  · subst h; simp [Matrix.one_apply]
  · simp [h, Matrix.one_apply]

lemma chanAdj_one : chanAdj (1 : Matrix (JReg d n) (JReg d n) ℂ) = 1 := by
  unfold chanAdj
  simp only [KK_one, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  push_cast
  rw [inv_mul_cancel₀ (by positivity), one_smul]


lemma chanAdj_psd {A : Matrix (JReg d n) (JReg d n) ℂ} (hA : A.PosSemidef) :
    (chanAdj A).PosSemidef := by
  unfold chanAdj
  have h : (∑ b : Fin n → Bool, ∑ r : Fin n → Fin d, (K b r)ᴴ * A * K b r).PosSemidef := by
    refine Matrix.posSemidef_sum _ (fun b _ => Matrix.posSemidef_sum _ (fun r _ => ?_))
    exact hA.conjTranspose_mul_mul_same _
  have hc : (0:ℂ) ≤ ((2:ℂ)^n)⁻¹ := by
    rw [inv_nonneg]; exact pow_nonneg (by norm_num) n
  exact h.smul hc

def chanAdjL : Matrix (JReg d n) (JReg d n) ℂ →ₗ[ℂ] Matrix (IReg d n) (IReg d n) ℂ where
  toFun := chanAdj
  map_add' A B := by
    unfold chanAdj
    rw [← smul_add, ← Finset.sum_add_distrib]
    congr 1; refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by
    unfold chanAdj
    simp only [RingHom.id_apply, Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul]
    simp only [smul_comm c]

lemma chanAdj_zero : chanAdj (0 : Matrix (JReg d n) (JReg d n) ℂ) = 0 :=
  map_zero (chanAdjL (d := d) (n := n))

lemma chanAdj_hasSum {f : ℕ → Matrix (JReg d n) (JReg d n) ℂ} {A : Matrix (JReg d n) (JReg d n) ℂ}
    (h : HasSum f A) : HasSum (fun i => chanAdj (f i)) (chanAdj A) := by
  have hc : Continuous (chanAdjL (d := d) (n := n)) := LinearMap.continuous_of_finiteDimensional _
  exact h.map (chanAdjL (d := d) (n := n)) hc

lemma K_iff (b : Fin n → Bool) (r : Fin n → Fin d) (j : JReg d n) (p : IReg d n) :
    (j = sel b p ∧ rest b p = r) ↔ ((fun i => (j i).1) = b ∧ p = unsel b j r) := by
  constructor
  · rintro ⟨rfl, rfl⟩
    refine ⟨rfl, ?_⟩
    obtain ⟨x, y⟩ := p
    simp only [unsel, sel, rest, Prod.mk.injEq]
    constructor <;> funext i <;> by_cases hb : b i <;> simp [hb]
  · rintro ⟨hl, rfl⟩
    constructor
    · funext i
      have := congrFun hl i
      simp only [sel, unsel] at this ⊢
      by_cases hb : b i
      · simp only [hb, if_true]; rw [hb] at this; ext <;> simp [this]
      · simp only [hb]; simp only [Bool.not_eq_true] at hb; rw [hb] at this; ext <;> simp [this]
    · funext i; by_cases hb : b i <;> simp [rest, unsel, hb]

lemma sumK (b : Fin n → Bool) (r : Fin n → Fin d) (j : JReg d n) (f : IReg d n → ℂ) :
    ∑ p, K b r j p * f p = if (fun i => (j i).1) = b then f (unsel b j r) else 0 := by
  unfold K
  simp only [K_iff, ite_mul, one_mul, zero_mul]
  by_cases hl : (fun i => (j i).1) = b
  · simp [hl]
  · simp [hl]

lemma sumK' (b : Fin n → Bool) (r : Fin n → Fin d) (j : JReg d n) (f : IReg d n → ℂ) :
    ∑ p, f p * K b r j p = if (fun i => (j i).1) = b then f (unsel b j r) else 0 := by
  rw [← sumK]; exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

lemma KRK (ρ σ : Mat d) (hρ : ρ.trace = 1) (hσ : σ.trace = 1) :
    ((2:ℂ)^n)⁻¹ • ∑ b : Fin n → Bool, ∑ r : Fin n → Fin d,
        K b r * jointInput n ρ σ * (K b r)ᴴ = powerState (labelledState ρ σ) n := by
  ext j j'
  simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    K_conj, smul_eq_mul]
  have step : ∀ b r, ∑ p', (∑ p, K b r j p * jointInput n ρ σ p p') * K b r j' p' =
      if (fun i => (j i).1) = b ∧ (fun i => (j' i).1) = b then
        jointInput n ρ σ (unsel b j r) (unsel b j' r) else 0 := by
    intro b r
    simp only [sumK]
    rw [sumK' b r j' (fun p' => if (fun i => (j i).1) = b then jointInput n ρ σ (unsel b j r) p' else 0)]
    by_cases h1 : (fun i => (j i).1) = b <;> by_cases h2 : (fun i => (j' i).1) = b <;> simp [h1, h2]
  simp only [step]
  have hPS : powerState (labelledState ρ σ) n j j' = ∏ i, labelledState ρ σ (j i) (j' i) := by
    simp [powerState, tensor, OptimalSpectrum.Entangled.kronFamily]
  rw [hPS]
  by_cases hl : (fun i => (j i).1) = (fun i => (j' i).1)
  · rw [Finset.sum_eq_single (fun i => (j i).1)]
    · simp only [hl, and_self, if_true]
      have hent : ∀ r, jointInput n ρ σ (unsel (fun i => (j' i).1) j r) (unsel (fun i => (j' i).1) j' r) =
          ∏ i, (if (j' i).1 then ρ (r i) (r i) * σ (j i).2 (j' i).2
            else ρ (j i).2 (j' i).2 * σ (r i) (r i)) := by
        intro r
        simp only [jointInput, Matrix.kronecker, Matrix.kroneckerMap_apply, QAlgorithms.piKron,
          Matrix.of_apply, unsel]
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl (fun i _ => ?_)
        by_cases hb : (j' i).1 <;> simp [hb]
      simp only [hent]
      rw [← Fintype.prod_sum (fun i c => if (j' i).1 = true then ρ c c * σ (j i).2 (j' i).2
        else ρ (j i).2 (j' i).2 * σ c c)]
      have hc : ((2:ℂ)^n)⁻¹ = ∏ _i : Fin n, (2:ℂ)⁻¹ := by simp [inv_pow]
      rw [hc, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      have hli : (j i).1 = (j' i).1 := congrFun hl i
      simp only [labelledState, hli, if_true]
      by_cases hb : (j' i).1
      · simp only [hb, if_true, ← Finset.sum_mul]
        rw [show ∑ c, ρ c c = ρ.trace from rfl, hρ, one_mul]
      · simp only [hb, Bool.false_eq_true, if_false, ← Finset.mul_sum]
        rw [show ∑ c, σ c c = σ.trace from rfl, hσ, mul_one]
    · intro b _ hb
      refine Finset.sum_eq_zero (fun r _ => ?_)
      rw [if_neg]; rintro ⟨h1, -⟩; exact hb h1.symm
    · simp
  · rw [Finset.sum_eq_zero (fun b _ => Finset.sum_eq_zero (fun r _ => ?_))]
    · have : ∃ i, (j i).1 ≠ (j' i).1 := by
        by_contra hc; push Not at hc; exact hl (funext hc)
      obtain ⟨i, hi⟩ := this
      rw [mul_zero, eq_comm]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [labelledState, hi])
    · rw [if_neg]; rintro ⟨h1, h2⟩; exact hl (h1.trans h2.symm)


lemma chanAdj_trace (ρ σ : Mat d) (hρ : ρ.trace = 1) (hσ : σ.trace = 1)
    (A : Matrix (JReg d n) (JReg d n) ℂ) :
    (chanAdj A * jointInput n ρ σ).trace = (A * powerState (labelledState ρ σ) n).trace := by
  rw [← KRK ρ σ hρ hσ]
  unfold chanAdj
  rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.mul_smul, Matrix.trace_smul]
  congr 1
  rw [Matrix.sum_mul, Matrix.trace_sum, Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Matrix.sum_mul, Matrix.trace_sum, Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (K b r)ᴴ]
  simp only [Matrix.mul_assoc]

/-! Spectral projections -/

def specProj {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℂ} (hG : G.IsHermitian)
    (B : Set ℝ) : Matrix ι ι ℂ :=
  ∑ i, B.indicator (fun _ => (1:ℂ)) (hG.eigenvalues i) • QAlgorithms.pureDensity (hG.eigenvectorBasis i)

lemma pure_psd {ι : Type*} [Fintype ι] [DecidableEq ι] (v : EuclideanSpace ℂ ι) :
    (QAlgorithms.pureDensity v).PosSemidef := by
  have : QAlgorithms.pureDensity v = Matrix.vecMulVec (fun a => v a) (star (fun a => v a)) := by
    ext a b; simp [QAlgorithms.pureDensity, Matrix.vecMulVec_apply]
  rw [this]
  exact Matrix.posSemidef_vecMulVec_self_star _

lemma specProj_psd {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℂ} (hG : G.IsHermitian)
    (B : Set ℝ) : (specProj hG B).PosSemidef := by
  unfold specProj
  refine Matrix.posSemidef_sum _ (fun i _ => ?_)
  refine (pure_psd _).smul ?_
  by_cases h : hG.eigenvalues i ∈ B <;> simp [h]

lemma specProj_empty {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℂ} (hG : G.IsHermitian) :
    specProj hG ∅ = 0 := by simp [specProj]

lemma specProj_univ {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℂ} (hG : G.IsHermitian) :
    specProj hG Set.univ = 1 := by
  unfold specProj
  simp only [Set.indicator_univ, one_smul]
  have hU := hG.eigenvectorUnitary.2
  rw [Matrix.mem_unitaryGroup_iff] at hU
  ext a b
  have := congrFun (congrFun hU a) b
  rw [Matrix.mul_apply] at this
  rw [Matrix.sum_apply, ← this]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [QAlgorithms.pureDensity, Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.star_apply]

lemma specProj_hasSum {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℂ} (hG : G.IsHermitian)
    (B : ℕ → Set ℝ) (hd : Pairwise (fun i j => Disjoint (B i) (B j))) :
    HasSum (fun k => specProj hG (B k)) (specProj hG (⋃ k, B k)) := by
  unfold specProj
  refine hasSum_sum (fun i _ => ?_)
  refine HasSum.smul_const ?_ _
  by_cases h : hG.eigenvalues i ∈ ⋃ k, B k
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 h
    rw [Set.indicator_of_mem h]
    have : ∀ k' ≠ k, (B k').indicator (fun _ => (1:ℂ)) (hG.eigenvalues i) = 0 := by
      intro k' hk'
      apply Set.indicator_of_notMem
      intro hk2
      exact Set.disjoint_left.1 (hd hk') hk2 hk
    have h1 := hasSum_single k this
    rwa [Set.indicator_of_mem hk] at h1
  · rw [Set.indicator_of_notMem h]
    have : ∀ k, (B k).indicator (fun _ => (1:ℂ)) (hG.eigenvalues i) = 0 := by
      intro k; apply Set.indicator_of_notMem
      intro hk; exact h (Set.mem_iUnion.2 ⟨k, hk⟩)
    simp only [this]; exact hasSum_zero


def measG {G : Matrix (JReg d n) (JReg d n) ℂ} (hG : G.IsHermitian) : TwoStateMeasurement d n where
  operator B := chanAdj (specProj hG B)
  empty := by rw [specProj_empty, chanAdj_zero]
  total := by rw [specProj_univ, chanAdj_one]
  positive B _ := chanAdj_psd (specProj_psd hG B)
  additive B _ hd := chanAdj_hasSum (specProj_hasSum hG B hd)

lemma pure_tr_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Matrix ι ι ℂ} (hR : R.PosSemidef)
    (v : EuclideanSpace ℂ ι) : 0 ≤ tr (R * QAlgorithms.pureDensity v) := by
  have := QAlgorithms.Measurements.born_nonnegative (pure_psd v) hR
  unfold QAlgorithms.effectProb at this; unfold tr
  rwa [Matrix.trace_mul_comm]

lemma law_eq {G : Matrix (JReg d n) (JReg d n) ℂ} (hG : G.IsHermitian) (ρ σ : Mat d)
    (hρ : Density ρ) (hσ : Density σ) :
    outcomeLaw (measG hG) ρ σ hρ hσ = spectralLaw G (powerState (labelledState ρ σ) n) := by
  have hR : (powerState (labelledState ρ σ) n).PosSemidef := powerState_psd (labelled_psd hρ hσ) n
  ext B hB
  rw [outcomeLaw, QAlgorithms.Measurements.bornLaw_apply _ _ _ B hB]
  change ENNReal.ofReal (QAlgorithms.effectProb (chanAdj (specProj hG B)) (jointInput n ρ σ)) = _
  unfold QAlgorithms.effectProb
  rw [chanAdj_trace ρ σ hρ.2 hσ.2]
  unfold spectralLaw
  rw [dif_pos hG, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hB, smul_eq_mul]
  unfold specProj
  rw [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : hG.eigenvalues i ∈ B
    · simp only [Set.indicator_of_mem h, one_smul, Pi.one_apply, mul_one]
      unfold tr; rw [Matrix.trace_mul_comm]
    · simp [Set.indicator_of_notMem h]
  · intro i _
    by_cases h : hG.eigenvalues i ∈ B
    · simp only [Set.indicator_of_mem h, one_smul]
      have := pure_tr_nonneg hR (hG.eigenvectorBasis i)
      unfold tr at this; rwa [Matrix.trace_mul_comm] at this
    · simp [Set.indicator_of_notMem h]

lemma spec_integrable {ι : Type*} [Fintype ι] [DecidableEq ι] (G R : Matrix ι ι ℂ) :
    Integrable (fun x : ℝ => x) (spectralLaw G R) := by
  unfold spectralLaw
  split_ifs with hG
  · refine (integrable_finsetSum_measure).2 (fun i _ => ?_)
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact integrable_zero_measure

lemma spec_mean {ι : Type*} [Fintype ι] [DecidableEq ι] {G R : Matrix ι ι ℂ} (hG : G.IsHermitian)
    (hR : R.PosSemidef) : ∫ x : ℝ, x ∂(spectralLaw G R) = tr (R * G) := by
  unfold spectralLaw
  rw [dif_pos hG, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    have hG' : G = ∑ i, (hG.eigenvalues i : ℂ) • QAlgorithms.pureDensity (hG.eigenvectorBasis i) := by
      conv_lhs => rw [hG.spectral_theorem, Unitary.conjStarAlgAut_apply]
      ext a b
      simp only [Matrix.sum_apply, Matrix.smul_apply, QAlgorithms.pureDensity, Matrix.of_apply,
        Matrix.mul_apply, Matrix.diagonal_apply, Function.comp_apply, smul_eq_mul]
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.star_apply]
      simp only [RCLike.star_def]; rw [mul_right_comm, mul_comm]; exact rfl
    conv_rhs => rw [hG']
    unfold tr
    rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hnn := pure_tr_nonneg hR (hG.eigenvectorBasis i)
    unfold tr at hnn
    rw [ENNReal.toReal_ofReal hnn]
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
    ring
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top


open Matrix OptimalTraceDistance.Estimation

def jinv {k n : ℕ} (e : Fin k ↪ Fin n) {i : Fin n} (h : i ∈ Set.range e) : Fin k := Classical.choose h

lemma e_jinv {k n : ℕ} (e : Fin k ↪ Fin n) {i : Fin n} (h : i ∈ Set.range e) : e (jinv e h) = i :=
  Classical.choose_spec h

lemma jinv_e {k n : ℕ} (e : Fin k ↪ Fin n) (j : Fin k) (h : e j ∈ Set.range e) : jinv e h = j :=
  e.injective (e_jinv e h)

lemma sum_cond {α β M : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [AddCommMonoid M] (C : Prop) [Decidable C] (a0 : α) (b0 : β) (f : α → β → M) :
    ∑ a, ∑ b, (if C ∧ a0 = a ∧ b0 = b then f a b else 0) = if C then f a0 b0 else 0 := by
  by_cases hC : C
  · simp only [hC, true_and, if_true]
    rw [Finset.sum_eq_single a0 (fun a _ ha => Finset.sum_eq_zero (fun b _ => if_neg (fun h => ha h.1.symm))) (by simp)]
    rw [Finset.sum_eq_single b0 (fun b _ hb => if_neg (fun h => hb h.2.symm)) (by simp)]
    simp
  · simp [hC]

lemma inner_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {k n : ℕ} (e : Fin k ↪ Fin n)
    (τ : Matrix ι ι ℂ) (hτ : τ.trace = 1) (a b : Fin k → ι) :
    ∑ x : Fin n → ι, ∑ y : Fin n → ι, (∏ i, τ (x i) (y i)) *
      ∏ i, (if h : i ∈ Set.range e then (if y i = a (jinv e h) ∧ x i = b (jinv e h) then (1:ℂ) else 0)
        else (if y i = x i then 1 else 0)) = ∏ j, τ (b j) (a j) := by
  set f : Fin n → ι → ι → ℂ := fun i c' c => τ c' c *
    (if h : i ∈ Set.range e then (if c = a (jinv e h) ∧ c' = b (jinv e h) then (1:ℂ) else 0)
      else (if c = c' then 1 else 0)) with hf
  have h1 : ∀ x y : Fin n → ι, (∏ i, τ (x i) (y i)) *
      ∏ i, (if h : i ∈ Set.range e then (if y i = a (jinv e h) ∧ x i = b (jinv e h) then (1:ℂ) else 0)
        else (if y i = x i then 1 else 0)) = ∏ i, f i (x i) (y i) := by
    intro x y; rw [← Finset.prod_mul_distrib]
  simp only [h1]
  have h2 : ∀ x : Fin n → ι, ∑ y : Fin n → ι, ∏ i, f i (x i) (y i) = ∏ i, ∑ c, f i (x i) c := by
    intro x; rw [Fintype.prod_sum (fun i c => f i (x i) c)]
  simp only [h2]
  rw [Fintype.prod_sum (fun i c' => ∑ c, f i c' c) |>.symm]
  have h3 : ∀ i, ∑ c', ∑ c, f i c' c =
      if h : i ∈ Set.range e then τ (b (jinv e h)) (a (jinv e h)) else 1 := by
    intro i
    by_cases h : i ∈ Set.range e
    · simp only [hf, dif_pos h]
      rw [Finset.sum_eq_single (b (jinv e h))]
      · rw [Finset.sum_eq_single (a (jinv e h))]
        · simp
        · intro c _ hc; simp [hc]
        · simp
      · intro c' _ hc'; refine Finset.sum_eq_zero (fun c _ => ?_); simp [hc']
      · simp
    · simp only [hf, dif_neg h]
      have : ∀ c', ∑ c, τ c' c * (if c = c' then (1:ℂ) else 0) = τ c' c' := by
        intro c'; simp
      simp only [this]; exact hτ
  simp only [h3]
  symm
  refine Fintype.prod_of_injective e e.injective _ _ (fun i hi => dif_neg hi) (fun j => ?_)
  rw [dif_pos (Set.mem_range_self j), jinv_e]

lemma trace_embed {ι : Type*} [Fintype ι] [DecidableEq ι] {k n : ℕ} (e : Fin k ↪ Fin n)
    (τ : Matrix ι ι ℂ) (hτ : τ.trace = 1) (H : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    (powerState τ n * embed e H).trace = (powerState τ k * H).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, powerState, tensor,
    OptimalSpectrum.Entangled.kronFamily, Matrix.of_apply]
  -- expand H (y∘e) (x∘e) as a sum over a b
  have hexp : ∀ x y : Fin n → ι, embed e H y x = ∑ a : Fin k → ι, ∑ b : Fin k → ι, H a b *
      ∏ i, (if h : i ∈ Set.range e then (if y i = a (jinv e h) ∧ x i = b (jinv e h) then 1 else 0)
        else (if y i = x i then 1 else 0)) := by
    intro x y
    have hprod : ∀ a b : Fin k → ι, (∏ i, (if h : i ∈ Set.range e then
        (if y i = a (jinv e h) ∧ x i = b (jinv e h) then (1:ℂ) else 0)
        else (if y i = x i then 1 else 0))) =
        if (∀ i, i ∉ Set.range e → y i = x i) ∧ (y ∘ e = a) ∧ (x ∘ e = b) then 1 else 0 := by
      intro a b
      have : ∀ i, (if h : i ∈ Set.range e then
          (if y i = a (jinv e h) ∧ x i = b (jinv e h) then (1:ℂ) else 0)
          else (if y i = x i then 1 else 0)) =
          if (if h : i ∈ Set.range e then (y i = a (jinv e h) ∧ x i = b (jinv e h)) else y i = x i)
            then 1 else 0 := by
        intro i; split_ifs <;> simp_all
      simp only [this, Fintype.prod_boole]
      congr 1
      apply propext
      constructor
      · intro hall
        refine ⟨fun i hi => ?_, ?_, ?_⟩
        · have := hall i; rwa [dif_neg hi] at this
        · funext j
          have := hall (e j); rw [dif_pos (Set.mem_range_self j), jinv_e] at this; exact this.1
        · funext j
          have := hall (e j); rw [dif_pos (Set.mem_range_self j), jinv_e] at this; exact this.2
      · rintro ⟨h1, rfl, rfl⟩ i
        by_cases hi : i ∈ Set.range e
        · rw [dif_pos hi]
          simp only [Function.comp_apply, e_jinv]; exact ⟨trivial, trivial⟩
        · rw [dif_neg hi]; exact h1 i hi
    simp only [hprod, mul_ite, mul_one, mul_zero]
    rw [sum_cond (∀ i, i ∉ Set.range e → y i = x i) (y ∘ e) (x ∘ e) (fun a b => H a b)]
    rfl
  simp only [hexp, Finset.mul_sum]
  conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  conv_lhs => enter [2, x, 2, a]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => ?_))
  have : ∀ x y : Fin n → ι, (∏ i, τ (x i) (y i)) * (H a b *
      ∏ i, (if h : i ∈ Set.range e then (if y i = a (jinv e h) ∧ x i = b (jinv e h) then (1:ℂ) else 0)
        else (if y i = x i then 1 else 0))) = H a b * ((∏ i, τ (x i) (y i)) *
      ∏ i, (if h : i ∈ Set.range e then (if y i = a (jinv e h) ∧ x i = b (jinv e h) then (1:ℂ) else 0)
        else (if y i = x i then 1 else 0))) := fun x y => by ring
  simp only [this, ← Finset.mul_sum]
  rw [inner_sum e τ hτ a b, mul_comm]


open Matrix OptimalTraceDistance.Estimation

lemma path_prod {ι : Type*} [Fintype ι] [DecidableEq ι] : ∀ (k : ℕ) (B : Fin k → Matrix ι ι ℂ) (a b : ι),
    (List.ofFn B).prod a b = ∑ u : Fin (k+1) → ι,
      (if u 0 = a ∧ u (Fin.last k) = b then (1:ℂ) else 0) * ∏ i : Fin k, B i (u i.castSucc) (u i.succ)
  | 0, B, a, b => by
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
    have h0 : ∀ c : ι, ((Equiv.funUnique (Fin 1) ι).symm c) 0 = c := fun c => rfl
    have hl : (Fin.last 0 : Fin 1) = 0 := rfl
    simp only [hl, h0]
    rw [Matrix.one_apply]
    by_cases h : a = b
    · subst h; simp
    · rw [if_neg h]; symm
      exact Finset.sum_eq_zero (fun c _ => if_neg (fun hc => h (hc.1.symm.trans hc.2)))
  | k+1, B, a, b => by
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    simp_rw [path_prod k]
    rw [← (Fin.consEquiv (fun _ => ι)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.prod_univ_succ, Fin.castSucc_zero,
      Fin.succ_zero_eq_one, Fin.cons_one, Fin.castSucc_succ, Fin.cons_succ, ← Fin.succ_last]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [Finset.sum_eq_single (u 0)]
      · by_cases hb : u (Fin.last k) = b <;> simp [hb]
      · intro c _ hc; simp [Ne.symm hc]
      · simp
    · intro c _ hc; refine Finset.sum_eq_zero (fun u _ => ?_); simp [hc]
    · simp

lemma cyc_trace {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) (B : Fin (m+1) → Matrix ι ι ℂ) :
    ∑ w : Fin (m+1) → ι, ∏ i : Fin (m+1), B i (w i) (w ⟨(i.val+1) % (m+1), Nat.mod_lt _ (by omega)⟩) =
      ((List.ofFn B).prod).trace := by
  simp only [Matrix.trace, Matrix.diag, path_prod]
  rw [Finset.sum_comm]
  have h1 : ∀ u : Fin (m+2) → ι, ∑ a, (if u 0 = a ∧ u (Fin.last (m+1)) = a then (1:ℂ) else 0) *
      ∏ i : Fin (m+1), B i (u i.castSucc) (u i.succ) =
      (if u 0 = u (Fin.last (m+1)) then (1:ℂ) else 0) * ∏ i : Fin (m+1), B i (u i.castSucc) (u i.succ) := by
    intro u
    rw [Finset.sum_eq_single (u 0)]
    · by_cases h : u 0 = u (Fin.last (m+1))
      · simp [h]
      · simp [h, Ne.symm h]
    · intro a _ ha; simp [Ne.symm ha]
    · simp
  simp only [h1]
  conv_rhs => rw [← (Fin.snocEquiv (fun _ => ι)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.snoc_last, Fin.snoc_castSucc]
  have h0 : (Fin.snoc w (w 0) : Fin (m+2) → ι) 0 = w 0 := by
    rw [show (0 : Fin (m+2)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
  rw [Finset.sum_eq_single (w 0)]
  · rw [h0, if_pos rfl, one_mul]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    congr 1
    by_cases hi : i.val + 1 < m + 1
    · have : i.succ = Fin.castSucc ⟨i.val + 1, hi⟩ := by ext; simp
      rw [this, Fin.snoc_castSucc]; congr 1; ext; simp [Nat.mod_eq_of_lt hi]
    · have hi' : i.val = m := by omega
      have : i.succ = Fin.last (m+1) := by ext; simp [hi']
      rw [this, Fin.snoc_last]; congr 1; ext; simp [hi']
  · intro c _ hc
    have : (Fin.snoc w c : Fin (m+2) → ι) 0 = w 0 := by
      rw [show (0 : Fin (m+2)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
    rw [this, if_neg (Ne.symm hc), zero_mul]
  · simp


lemma trace_shift {d : ℕ} (m : ℕ) (B : Fin (m+1) → Mat d) :
    (leftShift d (m+1) * tensor (m+1) B).trace = ((List.ofFn B).prod).trace := by
  rw [← cyc_trace]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, leftShift, tensor,
    OptimalSpectrum.Entangled.kronFamily, Matrix.of_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have : ∀ y : Fin (m+1) → Fin d, (∀ i : Fin (m+1), y i = u ⟨(i.val+1) % (m+1), Nat.mod_lt _ (by omega)⟩) ↔
      (fun i : Fin (m+1) => u ⟨(i.val+1) % (m+1), Nat.mod_lt _ (by omega)⟩) = y := by
    intro y; constructor
    · intro h; funext i; exact (h i).symm
    · rintro rfl i; rfl
  simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]


lemma tr2 {κ : Type*} [Fintype κ] (M N : Matrix κ κ ℂ) :
    (M * N).trace = ∑ x, ∑ y, M x y * N y x := by
  simp [Matrix.trace, Matrix.mul_apply]

lemma sum_split {d k : ℕ} (f : (Fin k → Bool × Fin d) → ℂ) :
    ∑ x, f x = ∑ b : Fin k → Bool, ∑ z : Fin k → Fin d, f (fun i => (b i, z i)) := by
  rw [← (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Bool) (fun _ => Fin d)).symm.sum_comp, Fintype.sum_prod_type]
  rfl

lemma label_sum {d k : ℕ} (ρ σ : Mat d) (w : Word d) (hk : w.factors.length = k) :
    (powerState (labelledState ρ σ) k * wordKernel w k).trace =
      (tensor k (fun i : Fin k => if (w.factors[i.val]?.getD (1,false)).2 then minus ρ σ else plus ρ σ) *
        (leftShift d k * tensor k (fun i : Fin k => if i.val = 0 then w.tail * (w.factors[i.val]?.getD (1,false)).1
          else (w.factors[i.val]?.getD (1,false)).1))).trace := by
  set t : Fin k → Bool := fun i => (w.factors[i.val]?.getD (1,false)).2 with ht
  set V := leftShift d k * tensor k (fun i : Fin k => if i.val = 0 then w.tail * (w.factors[i.val]?.getD (1,false)).1
          else (w.factors[i.val]?.getD (1,false)).1) with hV
  have hW : ∀ x y : Fin k → Bool × Fin d, wordKernel w k x y =
      if (fun i => (x i).1) = (fun i => (y i).1) then
        (∏ i, if t i && (x i).1 then (-1 : ℂ) else 1) * V (fun i => (x i).2) (fun i => (y i).2) else 0 := by
    intro x y
    have hWK : wordKernel w k = fun x y => if (fun i => (x i).1) = (fun i => (y i).1) then
        (∏ i, if t i && (x i).1 then (-1 : ℂ) else 1) * V (fun i => (x i).2) (fun i => (y i).2) else 0 := by
      unfold wordKernel; exact if_pos hk
    rw [hWK]
  rw [tr2, tr2]
  simp only [hW]
  rw [sum_split]
  simp only [sum_split (fun y => _ * _)]
  have hP : ∀ (b b' : Fin k → Bool) (z z' : Fin k → Fin d),
      powerState (labelledState ρ σ) k (fun i => (b i, z i)) (fun i => (b' i, z' i)) =
        ∏ i, labelledState ρ σ (b i, z i) (b' i, z' i) := by
    intro b b' z z'; simp [powerState, tensor, OptimalSpectrum.Entangled.kronFamily]
  simp only [hP]
  -- kill the b' sum
  have hkill : ∀ (b : Fin k → Bool) (z : Fin k → Fin d),
      ∑ b' : Fin k → Bool, ∑ z' : Fin k → Fin d, (∏ i, labelledState ρ σ (b i, z i) (b' i, z' i)) *
        (if (fun i => b' i) = (fun i => b i) then
          (∏ i, if t i && b' i then (-1 : ℂ) else 1) * V z' z else 0) =
      ∑ z' : Fin k → Fin d, (∏ i, (if t i && b i then (-1 : ℂ) else 1) *
          ((2:ℂ)⁻¹ * (if b i then σ (z i) (z' i) else ρ (z i) (z' i)))) * V z' z := by
    intro b z
    rw [Finset.sum_eq_single b]
    · refine Finset.sum_congr rfl (fun z' _ => ?_)
      simp only [if_true, labelledState, Finset.prod_mul_distrib]
      ring
    · intro b' _ hb'
      refine Finset.sum_eq_zero (fun z' _ => ?_)
      rw [if_neg (fun h => hb' h), mul_zero]
    · simp
  simp only [hkill]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z' _ => ?_)
  rw [← Finset.sum_mul]
  congr 1
  simp only [tensor, OptimalSpectrum.Entangled.kronFamily, Matrix.of_apply]
  rw [← Fintype.prod_sum (fun i c => (if t i && c then (-1 : ℂ) else 1) *
          ((2:ℂ)⁻¹ * (if c then σ (z i) (z' i) else ρ (z i) (z' i))))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [Fintype.sum_bool, minus, plus, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    smul_eq_mul, Bool.and_true, Bool.and_false, if_true, Bool.false_eq_true, if_false]
  by_cases hti : t i
  · rw [if_pos hti, if_pos hti]
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]; ring
  · rw [if_neg hti, if_neg hti]
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]; ring


lemma trace_wordKernel {d k : ℕ} (ρ σ : Mat d) (w : Word d) (hk : w.factors.length = k) (hk0 : 0 < k) :
    (powerState (labelledState ρ σ) k * wordKernel w k).trace =
      (wordEval w (plus ρ σ) (minus ρ σ)).trace := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m+1 := ⟨k-1, by omega⟩
  rw [label_sum ρ σ w hk, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [show tensor (m+1) (fun i : Fin (m+1) => if i.val = 0 then w.tail * (w.factors[i.val]?.getD (1,false)).1
          else (w.factors[i.val]?.getD (1,false)).1) *
        tensor (m+1) (fun i : Fin (m+1) => if (w.factors[i.val]?.getD (1,false)).2 then minus ρ σ else plus ρ σ) =
      tensor (m+1) (fun i : Fin (m+1) => (if i.val = 0 then w.tail * (w.factors[i.val]?.getD (1,false)).1
          else (w.factors[i.val]?.getD (1,false)).1) *
          (if (w.factors[i.val]?.getD (1,false)).2 then minus ρ σ else plus ρ σ)) from (kron_mul _ _).symm]
  rw [trace_shift]
  set g : Mat d × Bool → Mat d := fun At => At.1 * (if At.2 then minus ρ σ else plus ρ σ) with hg
  set G : Fin (m+1) → Mat d := fun i => g (w.factors[i.val]?.getD (1,false)) with hG
  have h1 : (fun i : Fin (m+1) => (if i.val = 0 then w.tail * (w.factors[i.val]?.getD (1,false)).1
          else (w.factors[i.val]?.getD (1,false)).1) *
          (if (w.factors[i.val]?.getD (1,false)).2 then minus ρ σ else plus ρ σ)) =
      fun i => if i.val = 0 then w.tail * G i else G i := by
    funext i; by_cases hi : i.val = 0 <;> simp [hi, hG, hg, Matrix.mul_assoc]
  rw [h1]
  have h2 : (List.ofFn (fun i : Fin (m+1) => if i.val = 0 then w.tail * G i else G i)).prod =
      w.tail * (List.ofFn G).prod := by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    simp only [Fin.val_zero, if_true, Fin.val_succ, Nat.add_one_ne_zero, if_false, Matrix.mul_assoc]
  have h3 : List.ofFn G = w.factors.map g := by
    apply List.ext_getElem
    · simp [hk]
    · intro i h1 h2
      simp only [List.getElem_ofFn, List.getElem_map, hG]
      rw [List.getElem?_eq_getElem (by simpa using h2), Option.getD_some]
  rw [h2, h3, Matrix.trace_mul_comm]
  rfl


lemma foldl_max_ge : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], a => by simp
  | (b :: l), a => by
    have ih := foldl_max_ge l (max a b)
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨le_trans (le_max_left a b) ih.1, fun x hx => ?_⟩
    rcases hx with rfl | hx
    · exact le_trans (le_max_right a x) ih.1
    · exact ih.2 x hx

lemma len_le_deg (g : TraceExpression d) (w : Word d) (hw : w ∈ g.words) :
    w.factors.length ≤ expressionDegree g :=
  (foldl_max_ge _ 0).2 _ (List.mem_map.mpr ⟨w, hw, rfl⟩)



/-! Symmetrization, Hermitian part, U-statistics -/

lemma perm_inv {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} (τ : Matrix ι ι ℂ)
    (π : Equiv.Perm (Fin k)) :
    (permutationOp (ι := ι) π)ᴴ * powerState τ k * permutationOp π = powerState τ k := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, permutationOp,
    OptimalSpectrum.Entangled.permOp, Matrix.of_apply, powerState, tensor,
    OptimalSpectrum.Entangled.kronFamily]
  simp only [apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Equiv.prod_comp π.symm (fun i => τ (x i) (y i))

lemma trace_symm {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} (τ : Matrix ι ι ℂ)
    (H : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    (powerState τ k * symmetrize H).trace = (powerState τ k * H).trace := by
  unfold symmetrize
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sum, Matrix.trace_sum]
  have : ∀ π : Equiv.Perm (Fin k), (powerState τ k * (permutationOp π * H * (permutationOp π)ᴴ)).trace =
      (powerState τ k * H).trace := by
    intro π
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, perm_inv]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast (Nat.factorial_pos k).ne'), one_mul]

lemma trace_hermPart_re {ι : Type*} [Fintype ι] {T : Matrix ι ι ℂ} (hT : T.IsHermitian)
    (A : Matrix ι ι ℂ) : (T * hermPart A).trace.re = (T * A).trace.re := by
  unfold hermPart
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.trace_add]
  have h : (T * Aᴴ).trace = star (T * A).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hT.eq, Matrix.trace_mul_comm]
  rw [h, smul_eq_mul, Complex.mul_re]
  simp [Complex.add_re, Complex.conj_re]
  ring

lemma trace_uStat {ι : Type*} [Fintype ι] [DecidableEq ι] {k n : ℕ} (hkn : k ≤ n)
    (τ : Matrix ι ι ℂ) (hτ : τ.trace = 1) (H : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    (powerState τ n * uStatistic n k H).trace = (powerState τ k * H).trace := by
  unfold uStatistic
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sum, Matrix.trace_sum]
  simp only [trace_embed _ τ hτ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
  have hc : (Fintype.card (Fin k ↪ Fin n) : ℂ) ≠ 0 := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
    exact_mod_cast (Nat.descFactorial_pos.2 hkn).ne' -- placeholder
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]


lemma wordKernel_ne {d k : ℕ} {w : Word d} (h : w.factors.length ≠ k) : wordKernel w k = 0 := by
  unfold wordKernel; exact if_neg h

lemma trace_list {d k : ℕ} (T : Matrix (Fin k → Bool × Fin d) (Fin k → Bool × Fin d) ℂ)
    (l : List (Word d)) (f : Word d → Matrix (Fin k → Bool × Fin d) (Fin k → Bool × Fin d) ℂ) :
    (T * (l.map f).sum).trace = (l.map (fun w => (T * f w).trace)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Matrix.mul_add, Matrix.trace_add, ih]

lemma trace_kernel {d k : ℕ} (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ) (g : TraceExpression d)
    (hk : 0 < k) :
    (powerState (labelledState ρ σ) k * expressionKernel g k).trace.re =
      (g.words.map (fun w => if w.factors.length = k then
        (wordEval w (plus ρ σ) (minus ρ σ)).trace else 0)).sum.re := by
  unfold expressionKernel
  rw [trace_hermPart_re (powerState_psd (labelled_psd hρ hσ) k).1, trace_symm, trace_list]
  congr 2
  refine List.map_congr_left (fun w _ => ?_)
  by_cases h : w.factors.length = k
  · rw [if_pos h, trace_wordKernel ρ σ w h hk]
  · rw [if_neg h, wordKernel_ne h, Matrix.mul_zero, Matrix.trace_zero]

lemma wordEval_zero {d : ℕ} (w : Word d) (X Y : Mat d) :
    (wordEval w 0 0).trace = if w.factors.length = 0 then (wordEval w X Y).trace else 0 := by
  rcases w with ⟨fs, tl⟩
  cases fs with
  | nil => simp [wordEval]
  | cons a l =>
    simp only [wordEval, List.length_cons, Nat.add_one_ne_zero, if_false, List.map_cons,
      List.prod_cons]
    simp

lemma split_list {d : ℕ} (l : List (Word d)) (D : ℕ) (hl : ∀ w ∈ l, w.factors.length ≤ D)
    (F : Word d → ℂ) :
    (l.map F).sum = (l.map (fun w => if w.factors.length = 0 then F w else 0)).sum +
      ∑ k ∈ Finset.Icc 1 D, (l.map (fun w => if w.factors.length = k then F w else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
    rw [ih (fun w hw => hl w (List.mem_cons_of_mem a hw))]
    have ha := hl a List.mem_cons_self
    have : ∑ k ∈ Finset.Icc 1 D, (if a.factors.length = k then F a else 0) =
        if a.factors.length = 0 then 0 else F a := by
      rw [Finset.sum_ite_eq]
      by_cases h0 : a.factors.length = 0
      · simp [h0]
      · rw [if_pos (Finset.mem_Icc.2 ⟨by omega, ha⟩), if_neg h0]
    rw [this]
    by_cases h0 : a.factors.length = 0 <;> simp [h0] <;> ring

lemma trace_one_powerState {d n : ℕ} (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ) :
    (powerState (labelledState ρ σ) n).trace = 1 := by
  rw [trace_powerState, trace_labelled hρ hσ, one_pow]

lemma mean_obs {d n : ℕ} (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ) (g : TraceExpression d)
    (hdeg : expressionDegree g ≤ n) :
    tr (powerState (labelledState ρ σ) n * observable g n) = (evaluate g (plus ρ σ) (minus ρ σ)).re := by
  unfold observable tr
  rw [Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    trace_one_powerState ρ σ hρ hσ, Matrix.mul_sum, Matrix.trace_sum, Complex.add_re, Complex.re_sum]
  have hL : (labelledState ρ σ).trace = 1 := trace_labelled hρ hσ
  have hk : ∀ k ∈ Finset.Icc 1 (expressionDegree g),
      (powerState (labelledState ρ σ) n * uStatistic n k (expressionKernel g k)).trace.re =
      (g.words.map (fun w => if w.factors.length = k then
        (wordEval w (plus ρ σ) (minus ρ σ)).trace else 0)).sum.re := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [trace_uStat (by omega) _ hL, trace_kernel ρ σ hρ hσ g (by omega)]
  rw [Finset.sum_congr rfl hk, ← Complex.re_sum]
  simp only [Complex.real_smul, mul_one, Complex.ofReal_re]
  rw [← Complex.add_re]
  congr 1
  unfold evaluate
  conv_rhs => rw [split_list g.words (expressionDegree g) (fun w hw => len_le_deg g w hw)
    (fun w => (wordEval w (plus ρ σ) (minus ρ σ)).trace)]
  rw [add_assoc]
  congr 3
  refine List.map_congr_left (fun w _ => ?_)
  exact wordEval_zero w _ _

end OTDProp27

open MeasureTheory OptimalTraceDistance.Estimation OTDProp27 in
theorem solution (d n : ℕ) (hd : 0 < d) (hn : 0 < n)
    (g : TraceExpression d) (hg : realOnHermitian g) (hdegree : expressionDegree g ≤ n) :
  (observable g n).IsHermitian ∧ inputCost n = n ∧
  ∃ M : TwoStateMeasurement d n, ∀ (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ),
    let μ := spectralLaw (observable g n) (powerState (labelledState ρ σ) n)
    outcomeLaw M ρ σ hρ hσ = μ ∧ Integrable (fun x : ℝ => x) μ ∧
      (∫ x : ℝ, x ∂μ) = (evaluate g (plus ρ σ) (minus ρ σ)).re := by
  refine ⟨obs_herm g n, rfl, measG (obs_herm g n), fun ρ σ hρ hσ => ?_⟩
  refine ⟨law_eq (obs_herm g n) ρ σ hρ hσ, spec_integrable _ _, ?_⟩
  rw [spec_mean (obs_herm g n) (powerState_psd (labelled_psd hρ hσ) n)]
  exact mean_obs ρ σ hρ hσ g hdegree
