-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P01.cloningFamilies_conjugateDegradable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T04:00:48.244269+00:00
-- url     : https://prove2.me/submissions/998413b3-cfb2-4ee4-9dba-38de8c6f1afd

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P01

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel)

namespace X7S1

/-- Kraus channels with an arbitrary finite index type. -/
lemma chan_of_kraus {ι κ K : Type*} [Fintype ι] [Fintype κ] [Fintype K] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) :
    IsChannel (krausApply E) := by
  let σ := Fintype.equivFin K
  refine ⟨Fintype.card K, fun j => E (σ.symm j), ?_, ?_⟩
  · unfold IsKrausFamily
    rw [← hE]
    exact Fintype.sum_equiv σ.symm _ _ (fun _ => rfl)
  · intro ρ
    unfold krausApply
    exact (Fintype.sum_equiv σ.symm _ _ (fun _ => rfl)).symm

lemma kraus_comp {ι κ μ K L : Type*} [Fintype ι] [Fintype κ] [Fintype μ] [Fintype K] [Fintype L]
    (E : K → Matrix κ ι ℂ) (F : L → Matrix μ κ ℂ) (ρ : Matrix ι ι ℂ) :
    krausApply F (krausApply E ρ) = krausApply (fun p : K × L => F p.2 * E p.1) ρ := by
  unfold krausApply
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma chan_comp {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ] {_i1 : DecidableEq ι} {_i2 : DecidableEq κ}
    (Φ : Superop ι κ) (Ψ : Superop κ μ) (hΦ : IsChannel Φ) (hΨ : IsChannel Ψ) :
    IsChannel (Ψ ∘ Φ) := by
  obtain ⟨m, E, hE, hΦE⟩ := hΦ
  obtain ⟨n, F, hF, hΨF⟩ := hΨ
  have h : Ψ ∘ Φ = krausApply (fun p : Fin m × Fin n => F p.2 * E p.1) := by
    funext ρ
    simp only [Function.comp, hΦE, hΨF, kraus_comp]
  rw [h]
  apply chan_of_kraus
  rw [Fintype.sum_prod_type]
  unfold IsKrausFamily at hE hF
  rw [← hE]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Matrix.conjTranspose_mul]
  have : ∀ j : Fin n, (E k)ᴴ * (F j)ᴴ * (F j * E k) = (E k)ᴴ * ((F j)ᴴ * F j) * E k := by
    intro j; simp [Matrix.mul_assoc]
  simp only [this, ← Matrix.sum_mul, ← Matrix.mul_sum, hF, Matrix.mul_one]

lemma kraus_smul {ι κ K : Type*} [Fintype ι] [Fintype κ] [Fintype K]
    (E : K → Matrix κ ι ℂ) (z : ℂ) (ρ : Matrix ι ι ℂ) :
    krausApply E (z • ρ) = z • krausApply E ρ := by
  unfold krausApply
  rw [Finset.smul_sum]
  simp [Matrix.mul_smul, Matrix.smul_mul]

lemma kraus_add {ι κ K : Type*} [Fintype ι] [Fintype κ] [Fintype K]
    (E : K → Matrix κ ι ℂ) (ρ σ : Matrix ι ι ℂ) :
    krausApply E (ρ + σ) = krausApply E ρ + krausApply E σ := by
  unfold krausApply
  rw [← Finset.sum_add_distrib]
  simp [Matrix.mul_add, Matrix.add_mul]

/-- The entrywise-conjugated Kraus family implements the transposed channel. -/
lemma kraus_conj_transpose {ι κ K : Type*} [Fintype ι] [Fintype κ] [Fintype K]
    (E : K → Matrix κ ι ℂ) (ρ : Matrix ι ι ℂ) :
    krausApply (fun k => (E k).map (starRingEnd ℂ)) ρᵀ = (krausApply E ρ)ᵀ := by
  unfold krausApply
  rw [Matrix.transpose_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  show (E k).map (starRingEnd ℂ) * (ρᵀ * ((E k).map (starRingEnd ℂ))ᴴ) = _
  rw [show ((E k).map (starRingEnd ℂ))ᴴ = (E k)ᵀ from by
        ext i j; simp [Matrix.conjTranspose_apply],
      show (E k)ᴴᵀ = (E k).map (starRingEnd ℂ) from by
        ext i j; simp [Matrix.conjTranspose_apply]]

lemma conj_kraus_family {ι κ K : Type*} [Fintype ι] [Fintype κ] [Fintype K] [DecidableEq ι]
    (E : K → Matrix κ ι ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) :
    ∑ k, ((E k).map (starRingEnd ℂ))ᴴ * (E k).map (starRingEnd ℂ) = 1 := by
  have h := congrArg (fun M : Matrix ι ι ℂ => M.map (starRingEnd ℂ)) hE
  rw [Matrix.map_one (starRingEnd ℂ) (map_zero _) (map_one _)] at h
  rw [← h]
  ext i j
  simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply]

lemma chan_conj {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (Φ : Superop ι κ) (hΦ : IsChannel Φ) :
    ∃ G : Superop ι κ, IsChannel G ∧ ∀ ρ, G ρᵀ = (Φ ρ)ᵀ := by
  obtain ⟨m, E, hE, hΦE⟩ := hΦ
  refine ⟨krausApply (fun k => (E k).map (starRingEnd ℂ)), chan_of_kraus _ ?_, ?_⟩
  · exact conj_kraus_family E hE
  · intro ρ; rw [hΦE]; exact kraus_conj_transpose E ρ

end X7S1

end QAlgorithms.Papers.Independent.Support50.P01

end


noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P01

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel)

namespace X7CF

variable {a bb e P : ℕ}

/-- Shift-type isometry `U|k⟩ = Σ_i w(k,i) |k+i⟩|i⟩`. -/
def shiftU (w : ℕ → ℕ → ℝ) : Matrix (Fin bb × Fin e) (Fin a) ℂ :=
  fun be k => if be.1.val = k.val + be.2.val then ((w k.val be.2.val : ℝ) : ℂ) else 0

lemma conj_entry {ι κ : Type*} [Fintype ι] (A : Matrix κ ι ℂ) (Y : Matrix ι ι ℂ) (x y : κ) :
    (A * Y * Aᴴ) x y = ∑ u, ∑ v, A x u * conj (A y v) * Y u v := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
  simp only [RCLike.star_def]; ring

lemma swap3 {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M]
    (f : α → β → γ → M) :
    ∑ i, ∑ k, ∑ k', f i k k' = ∑ k, ∑ k', ∑ i, f i k k' := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]

lemma recv (w : ℕ → ℕ → ℝ) (X : Matrix (Fin a) (Fin a) ℂ) (b b' : Fin bb) :
    receiverChannel (shiftU (bb := bb) (e := e) w) X b b' =
      ∑ k : Fin a, ∑ k' : Fin a, ((∑ i : Fin e, if b.val = k.val + i.val ∧ b'.val = k'.val + i.val then
        w k.val i.val * w k'.val i.val else 0 : ℝ) : ℂ) * X k k' := by
  simp only [receiverChannel, traceRight, Matrix.of_apply, conj_entry]
  rw [swap3]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun k' _ => ?_))
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [shiftU]
  by_cases h1 : b.val = k.val + i.val <;> by_cases h2 : b'.val = k'.val + i.val <;>
    simp [h1, h2]

lemma comp (w : ℕ → ℕ → ℝ) (hb : ∀ k : Fin a, ∀ i : Fin e, k.val + i.val < bb)
    (X : Matrix (Fin a) (Fin a) ℂ) (i i' : Fin e) :
    complementaryChannel (shiftU (bb := bb) (e := e) w) X i i' =
      ∑ k : Fin a, ∑ k' : Fin a, ((if k.val + i.val = k'.val + i'.val then
        w k.val i.val * w k'.val i'.val else 0 : ℝ) : ℂ) * X k k' := by
  simp only [complementaryChannel, traceLeft, Matrix.of_apply, conj_entry]
  rw [swap3]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun k' _ => ?_))
  rw [Finset.sum_eq_single (⟨k.val + i.val, hb k i⟩ : Fin bb)]
  · simp only [shiftU]
    by_cases h : k.val + i.val = k'.val + i'.val <;> simp [h]
  · intro b _ hne
    have : b.val ≠ k.val + i.val := fun h => hne (Fin.ext h)
    simp [shiftU, this]
  · simp

lemma iso (w : ℕ → ℕ → ℝ) (hb : ∀ k : Fin a, ∀ i : Fin e, k.val + i.val < bb)
    (hw : ∀ k : Fin a, ∑ i : Fin e, w k.val i.val * w k.val i.val = 1) :
    (shiftU (a := a) (bb := bb) (e := e) w)ᴴ * (shiftU (a := a) (bb := bb) (e := e) w) = 1 := by
  refine Matrix.ext fun k k' => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, shiftU, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have : ∀ i : Fin e, (∑ b : Fin bb,
      star (if b.val = k.val + i.val then ((w k.val i.val : ℝ) : ℂ) else 0) *
        (if b.val = k'.val + i.val then ((w k'.val i.val : ℝ) : ℂ) else 0)) =
      if k = k' then ((w k.val i.val * w k.val i.val : ℝ) : ℂ) else 0 := by
    intro i
    rw [Finset.sum_eq_single (⟨k.val + i.val, hb k i⟩ : Fin bb)]
    · by_cases h : k = k'
      · subst h; simp
      · have : k.val + i.val ≠ k'.val + i.val := fun h' => h (Fin.ext (by omega))
        have h' : k.val ≠ k'.val := fun h' => h (Fin.ext h')
        simp [h, this, h']
    · intro b _ hne
      have : b.val ≠ k.val + i.val := fun h => hne (Fin.ext h)
      simp [this]
    · simp
  simp only [this]
  by_cases h : k = k'
  · subst h; simp only [if_true, Matrix.one_apply_eq]; rw [← Complex.ofReal_sum, hw k]; simp
  · simp [h, Matrix.one_apply_ne h]

/-- Shift-type Kraus operator `K_p = Σ_j κ(p,j) |j⟩⟨p+j|`. -/
def shiftK (κ : ℕ → ℕ → ℝ) (p : Fin P) : Matrix (Fin e) (Fin bb) ℂ :=
  fun j b => if b.val = p.val + j.val then ((κ p.val j.val : ℝ) : ℂ) else 0

/-- Witness: `α`-weighted shift Kraus family plus `γ`-weighted completely depolarizing part. -/
def wit (κ : ℕ → ℕ → ℝ) (sα sγ : ℝ) :
    (Fin P ⊕ (Fin e × Fin bb)) → Matrix (Fin e) (Fin bb) ℂ
  | Sum.inl p => ((sα : ℝ) : ℂ) • shiftK κ p
  | Sum.inr q => ((sγ : ℝ) : ℂ) • Matrix.single q.1 q.2 1

lemma kraus_entry {K ι κ : Type*} [Fintype K] [Fintype ι] (E : K → Matrix κ ι ℂ)
    (Y : Matrix ι ι ℂ) (j j' : κ) :
    krausApply E Y j j' = ∑ b, ∑ b', ∑ q, E q j b * conj (E q j' b') * Y b b' := by
  simp only [krausApply, Matrix.sum_apply, conj_entry]
  rw [swap3]

lemma wit_apply (κ : ℕ → ℕ → ℝ) (sα sγ : ℝ) (Y : Matrix (Fin bb) (Fin bb) ℂ) (j j' : Fin e) :
    krausApply (wit (P := P) κ sα sγ) Y j j' =
      ∑ b, ∑ b', ((sα * sα * ∑ p : Fin P,
          (if b.val = p.val + j.val ∧ b'.val = p.val + j'.val then κ p j * κ p j' else 0)
        + (if j = j' ∧ b = b' then sγ * sγ else 0) : ℝ) : ℂ) * Y b b' := by
  rw [kraus_entry]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun b' _ => ?_))
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [wit, shiftK, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  push_cast
  rw [add_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h1 : b.val = p.val + j.val <;> by_cases h2 : b'.val = p.val + j'.val <;>
      simp [h1, h2] <;> ring_nf <;> simp
  · by_cases hj : j = j' <;> by_cases hb : b = b' <;>
      simp [hj, hb, Finset.mul_sum, Finset.sum_mul, ite_and] <;> ring

lemma sum_fin_eq_single {n : ℕ} (t : ℕ) (ht : t < n) (f : Fin n → ℝ) :
    ∑ b : Fin n, (if b.val = t then f b else 0) = f ⟨t, ht⟩ := by
  rw [Finset.sum_eq_single (⟨t, ht⟩ : Fin n)]
  · simp
  · intro b _ hne
    have : b.val ≠ t := fun h => hne (Fin.ext h)
    simp [this]
  · simp

lemma wit_family (κ : ℕ → ℕ → ℝ) (sα sγ : ℝ)
    (hK : ∀ b : Fin bb, ∑ p : Fin P, ∑ j : Fin e,
      (if b.val = p.val + j.val then κ p j * κ p j else 0) = 1)
    (hs : sα * sα + e * (sγ * sγ) = 1) :
    ∑ q, (wit (P := P) (e := e) (bb := bb) κ sα sγ q)ᴴ * wit κ sα sγ q = 1 := by
  refine Matrix.ext fun b b' => ?_
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Matrix.add_apply]
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, wit, shiftK,
    Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  by_cases hbb : b = b'
  · subst hbb
    rw [Matrix.one_apply_eq]
    have h1 := hK b
    have : ∀ p : Fin P, ∀ j : Fin e,
        star (((sα : ℝ) : ℂ) * if b.val = p.val + j.val then ((κ p j : ℝ) : ℂ) else 0) *
          (((sα : ℝ) : ℂ) * if b.val = p.val + j.val then ((κ p j : ℝ) : ℂ) else 0) =
        (((sα * sα * if b.val = p.val + j.val then κ p j * κ p j else 0) : ℝ) : ℂ) := by
      intro p j; by_cases h : b.val = p.val + j.val <;> simp [h] <;> ring
    simp only [this]
    have h2 : ∀ c : Fin e, ∑ c_1 : Fin bb, ∑ j : Fin e,
        star (((sγ : ℝ) : ℂ) * if c = j ∧ c_1 = b then (1 : ℂ) else 0) *
          (((sγ : ℝ) : ℂ) * if c = j ∧ c_1 = b then (1 : ℂ) else 0) = ((sγ * sγ : ℝ) : ℂ) := by
      intro c
      have : ∀ c1 : Fin bb, ∀ j : Fin e, star (((sγ : ℝ) : ℂ) * if c = j ∧ c1 = b then (1 : ℂ) else 0) *
          (((sγ : ℝ) : ℂ) * if c = j ∧ c1 = b then (1 : ℂ) else 0) =
          if c1 = b then (if j = c then ((sγ * sγ : ℝ) : ℂ) else 0) else 0 := by
        intro c1 j
        by_cases h : c = j <;> by_cases h' : c1 = b <;> simp [h, h', eq_comm]
      simp only [this]
      rw [Finset.sum_eq_single b (fun x _ h => by simp [h]) (by simp)]
      simp
    simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h3 : (∑ x : Fin P, ∑ x_1 : Fin e, (((sα * sα * if b.val = x.val + x_1.val then
        κ x x_1 * κ x x_1 else 0) : ℝ) : ℂ)) = ((sα * sα : ℝ) : ℂ) := by
      calc _ = (((sα * sα) * ∑ p : Fin P, ∑ j : Fin e,
            (if b.val = p.val + j.val then κ p j * κ p j else 0) : ℝ) : ℂ) := by
              push_cast; simp only [Finset.mul_sum]
        _ = _ := by rw [h1, mul_one]
    rw [h3, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_add, hs]; simp
  · rw [Matrix.one_apply_ne hbb]
    have hv : b.val ≠ b'.val := fun h => hbb (Fin.ext h)
    rw [show (0:ℂ) = 0 + 0 by simp]
    congr 1
    · refine Finset.sum_eq_zero (fun p _ => Finset.sum_eq_zero (fun j _ => ?_))
      by_cases h1 : b.val = p.val + j.val <;> by_cases h2 : b'.val = p.val + j.val <;>
        simp [h1, h2]
      omega
    · refine Finset.sum_eq_zero (fun c _ => Finset.sum_eq_zero (fun c1 _ =>
        Finset.sum_eq_zero (fun j _ => ?_)))
      by_cases h1 : c = j ∧ c1 = b <;> by_cases h2 : c = j ∧ c1 = b' <;> simp [h1, h2] <;>
        first | exact fun h => absurd h hbb | exact Or.inl fun h => absurd h.symm hbb

lemma sum2_single {n m : ℕ} (t1 t2 : ℕ) (h1 : t1 < n) (h2 : t2 < m) (C : ℝ) :
    ∑ b : Fin n, ∑ b' : Fin m, (if b.val = t1 ∧ b'.val = t2 then C else 0) = C := by
  rw [Finset.sum_eq_single (⟨t1, h1⟩ : Fin n)]
  · rw [Finset.sum_eq_single (⟨t2, h2⟩ : Fin m)]
    · simp
    · intro b' _ hne
      have : b'.val ≠ t2 := fun h => hne (Fin.ext h)
      simp [this]
    · simp
  · intro b _ hne
    have : b.val ≠ t1 := fun h => hne (Fin.ext h)
    simp [this]
  · simp

lemma swap4 {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [AddCommMonoid M] (f : α → β → γ → δ → M) :
    ∑ x, ∑ y, ∑ z, ∑ t, f x y z t = ∑ z, ∑ t, ∑ x, ∑ y, f x y z t := by
  calc ∑ x, ∑ y, ∑ z, ∑ t, f x y z t = ∑ x, ∑ z, ∑ y, ∑ t, f x y z t :=
        Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
    _ = ∑ z, ∑ x, ∑ y, ∑ t, f x y z t := Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ t, ∑ y, f x y z t :=
        Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun x _ => Finset.sum_comm))
    _ = ∑ z, ∑ t, ∑ x, ∑ y, f x y z t := Finset.sum_congr rfl (fun z _ => Finset.sum_comm)

lemma coef_collapse (w κ : ℕ → ℕ → ℝ) (sα sγ : ℝ)
    (hb : ∀ k : Fin a, ∀ i : Fin e, k.val + i.val < bb)
    (hbK : ∀ p : Fin P, ∀ j : Fin e, p.val + j.val < bb) (j j' : Fin e) (k k' : Fin a) :
    ∑ b : Fin bb, ∑ b' : Fin bb, (sα * sα * ∑ p : Fin P,
          (if b.val = p.val + j.val ∧ b'.val = p.val + j'.val then κ p j * κ p j' else 0)
        + (if j = j' ∧ b = b' then sγ * sγ else 0)) *
      (∑ i : Fin e, if b.val = k.val + i.val ∧ b'.val = k'.val + i.val then
        w k.val i.val * w k'.val i.val else 0) =
    sα * sα * ∑ p : Fin P, ∑ i : Fin e,
      (if p.val + j.val = k.val + i.val ∧ p.val + j'.val = k'.val + i.val then
        κ p j * κ p j' * (w k i * w k' i) else 0)
      + (if j = j' ∧ k = k' then sγ * sγ * ∑ i : Fin e, w k i * w k i else 0) := by
  rw [Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun b' _ => add_mul _ _ _))]
  simp only [Finset.sum_add_distrib]
  congr 1
  · simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [swap4, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun i _ => ?_))
    rw [← sum2_single (n := bb) (m := bb) (p.val + j.val) (p.val + j'.val) (hbK p j) (hbK p j')
      (sα * (sα * (if p.val + j.val = k.val + i.val ∧ p.val + j'.val = k'.val + i.val then
        κ p j * (κ p j' * (w k i * w k' i)) else 0)))]
    refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun b' _ => ?_))
    split_ifs <;> (try ring) <;> (exfalso; omega)
  · by_cases hj : j = j'
    · simp only [hj, true_and]
      have : ∀ b : Fin bb, ∑ b' : Fin bb, (if b = b' then sγ * sγ else 0) *
          (∑ i : Fin e, if b.val = k.val + i.val ∧ b'.val = k'.val + i.val then
            w k.val i.val * w k'.val i.val else 0) =
          sγ * sγ * ∑ i : Fin e, if b.val = k.val + i.val ∧ b.val = k'.val + i.val then
            w k.val i.val * w k'.val i.val else 0 := by
        intro b
        rw [Finset.sum_eq_single b (fun b' _ h => by simp [Ne.symm h]) (by simp)]
        simp
      simp only [this, ← Finset.mul_sum]
      rw [Finset.sum_comm]
      by_cases hk : k = k'
      · subst hk
        simp only [and_self, if_true]
        congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [sum_fin_eq_single _ (hb k i)]
      · simp only [hk, if_false]
        have hk' : k.val ≠ k'.val := fun h => hk (Fin.ext h)
        rw [Finset.sum_eq_zero, mul_zero]
        intro i _
        refine Finset.sum_eq_zero (fun b _ => ?_)
        rw [if_neg]; omega
    · simp [hj]

lemma reorder {α β : Type*} [Fintype α] [Fintype β] (c : α → α → ℝ) (d : α → α → β → β → ℝ)
    (X : Matrix β β ℂ) :
    ∑ x, ∑ y, ((c x y : ℝ) : ℂ) * ∑ k, ∑ k', ((d x y k k' : ℝ) : ℂ) * X k k' =
      ∑ k, ∑ k', ((∑ x, ∑ y, c x y * d x y k k' : ℝ) : ℂ) * X k k' := by
  simp only [Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul, Complex.ofReal_mul]
  rw [swap4]
  refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ =>
    Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))))

lemma main_red (w κ : ℕ → ℕ → ℝ) (sα sγ : ℝ)
    (hb : ∀ k : Fin a, ∀ i : Fin e, k.val + i.val < bb)
    (hbK : ∀ p : Fin P, ∀ j : Fin e, p.val + j.val < bb)
    (hcoef : ∀ (j j' : Fin e) (k k' : Fin a),
      sα * sα * ∑ p : Fin P, ∑ i : Fin e,
        (if p.val + j.val = k.val + i.val ∧ p.val + j'.val = k'.val + i.val then
          κ p j * κ p j' * (w k i * w k' i) else 0)
      + (if j = j' ∧ k = k' then sγ * sγ * ∑ i : Fin e, w k i * w k i else 0) =
      if k.val + j'.val = k'.val + j.val then w k j' * w k' j else 0)
    (X : Matrix (Fin a) (Fin a) ℂ) :
    krausApply (wit (P := P) κ sα sγ) (receiverChannel (shiftU (bb := bb) (e := e) w) X) =
      (complementaryChannel (shiftU (bb := bb) (e := e) w) X)ᵀ := by
  refine Matrix.ext fun j j' => ?_
  rw [wit_apply, Matrix.transpose_apply, comp w hb]
  simp only [recv]
  refine (reorder _ _ X).trans ?_
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun k' _ => ?_))
  rw [coef_collapse w κ sα sγ hb hbK, hcoef]

lemma main_cd (w κ : ℕ → ℕ → ℝ) (sα sγ : ℝ)
    (hb : ∀ k : Fin a, ∀ i : Fin e, k.val + i.val < bb)
    (hbK : ∀ p : Fin P, ∀ j : Fin e, p.val + j.val < bb)
    (hw : ∀ k : Fin a, ∑ i : Fin e, w k.val i.val * w k.val i.val = 1)
    (hK : ∀ b : Fin bb, ∑ p : Fin P, ∑ j : Fin e,
      (if b.val = p.val + j.val then κ p j * κ p j else 0) = 1)
    (hs : sα * sα + e * (sγ * sγ) = 1)
    (hcoef : ∀ (j j' : Fin e) (k k' : Fin a),
      sα * sα * ∑ p : Fin P, ∑ i : Fin e,
        (if p.val + j.val = k.val + i.val ∧ p.val + j'.val = k'.val + i.val then
          κ p j * κ p j' * (w k i * w k' i) else 0)
      + (if j = j' ∧ k = k' then sγ * sγ * ∑ i : Fin e, w k i * w k i else 0) =
      if k.val + j'.val = k'.val + j.val then w k j' * w k' j else 0) :
    ConjugateDegradable (shiftU (a := a) (bb := bb) (e := e) w) := by
  refine ⟨iso w hb hw, krausApply (wit (P := P) κ sα sγ), ?_, main_red w κ sα sγ hb hbK hcoef⟩
  convert X7S1.chan_of_kraus _ (wit_family (P := P) (e := e) (bb := bb) κ sα sγ hK hs)

end X7CF

end QAlgorithms.Papers.Independent.Support50.P01

end


noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P01

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace X7CF1

lemma cc0 (N k : ℕ) (hk : k ≤ N) :
    cloningCoefficient N (N+1) k 0 = ((N + 1 - k : ℕ) : ℝ) / (N + 2) := by
  unfold cloningCoefficient
  have h1 : N + 1 - N = 1 := by omega
  have h2 : N + 1 - k - 0 = (N - k) + 1 := by omega
  have h3 : N + 1 - k = (N - k) + 1 := by omega
  rw [h1, h2, h3, add_zero, Nat.factorial_succ (N - k), Nat.factorial_succ (N + 1)]
  simp only [Nat.sub_zero, Nat.factorial_one, Nat.factorial_zero]
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  have : ((N - k).factorial : ℝ) ≠ 0 := by positivity
  have : ((N + 1).factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma cc1 (N k : ℕ) (hk : k ≤ N) :
    cloningCoefficient N (N+1) k 1 = ((k + 1 : ℕ) : ℝ) / (N + 2) := by
  unfold cloningCoefficient
  rw [show N + 1 - N = 1 by omega, show N + 1 - k - 1 = N - k by omega,
    Nat.factorial_succ k, Nat.factorial_succ (N + 1)]
  simp only [Nat.sub_self, Nat.factorial_one, Nat.factorial_zero]
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  have : ((N - k).factorial : ℝ) ≠ 0 := by positivity
  have : ((N + 1).factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Atom-form amplitudes of the `(N, N+1)` cloner. -/
def u1 (N : ℕ) : ℕ → ℕ → ℝ := fun k i =>
  if i = 0 then Real.sqrt ((N + 1 - k : ℕ) : ℝ) / Real.sqrt ((N : ℝ) + 2)
  else Real.sqrt ((k + 1 : ℕ) : ℝ) / Real.sqrt ((N : ℝ) + 2)

/-- Kraus amplitudes of the symmetric single-qubit marginal `Sym^{N+1} → ℂ²`. -/
def κ1 (N : ℕ) : ℕ → ℕ → ℝ := fun p j =>
  if j = 0 then Real.sqrt ((N + 1 - p : ℕ) : ℝ) / Real.sqrt ((N : ℝ) + 1)
  else Real.sqrt ((p + 1 : ℕ) : ℝ) / Real.sqrt ((N : ℝ) + 1)

lemma finE_val (N : ℕ) (i : Fin (N + 1 - N + 1)) : i.val = 0 ∨ i.val = 1 := by
  have := i.isLt; omega

lemma sumE (N : ℕ) (f : ℕ → ℝ) : ∑ i : Fin (N + 1 - N + 1), f i.val = f 0 + f 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => f i), show N + 1 - N + 1 = 2 by omega]
  simp [Finset.sum_range_succ]

lemma dil_eq (N : ℕ) : clonerDilation N (N + 1) = X7CF.shiftU (u1 N) := by
  ext ⟨b, i⟩ k
  simp only [clonerDilation, X7CF.shiftU]
  split_ifs with h
  · congr 1
    have hk := k.isLt
    rcases finE_val N i with hi | hi
    · rw [hi, cc0 N k (by omega), Real.sqrt_div' _ (by positivity)]
      simp [u1]
    · rw [hi, cc1 N k (by omega), Real.sqrt_div' _ (by positivity)]
      simp [u1]
  · rfl

lemma msq (m : ℕ) (x : ℝ) (hx : 0 < x) :
    Real.sqrt (m : ℝ) / Real.sqrt x * (Real.sqrt (m : ℝ) / Real.sqrt x) = m / x := by
  rw [div_mul_div_comm, Real.mul_self_sqrt (Nat.cast_nonneg _), Real.mul_self_sqrt hx.le]

lemma hw1 (N : ℕ) (k : Fin (N + 1)) :
    ∑ i : Fin (N + 1 - N + 1), u1 N k.val i.val * u1 N k.val i.val = 1 := by
  rw [sumE N (fun i => u1 N k.val i * u1 N k.val i)]
  simp only [u1, if_true, one_ne_zero, if_false]
  rw [msq _ _ (by positivity), msq _ _ (by positivity)]
  have hk := k.isLt
  push_cast [Nat.cast_sub (show k.val ≤ N + 1 by omega)]
  field_simp
  ring

lemma srs (L t : ℕ) (f : ℕ → ℝ) (hf : ∀ p, p ≠ t → f p = 0) :
    ∑ p ∈ Finset.range L, f p = if t < L then f t else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single t (fun p _ hp => hf p hp) (by simp [h])]
  · exact Finset.sum_eq_zero (fun p hp => hf p (by simp at hp; omega))

lemma hK1 (N : ℕ) (b : Fin (N + 1 + 1)) :
    ∑ p : Fin (N + 1), ∑ j : Fin (N + 1 - N + 1),
      (if b.val = p.val + j.val then κ1 N p j * κ1 N p j else 0) = 1 := by
  refine (Finset.sum_congr rfl (fun p _ => sumE N (fun j =>
    if b.val = p.val + j then κ1 N p.val j * κ1 N p.val j else 0))).trans ?_
  rw [Finset.sum_add_distrib]
  rw [Fin.sum_univ_eq_sum_range (fun p => if b.val = p + 0 then κ1 N p 0 * κ1 N p 0 else 0),
    Fin.sum_univ_eq_sum_range (fun p => if b.val = p + 1 then κ1 N p 1 * κ1 N p 1 else 0)]
  rw [srs (N + 1) b.val _ (fun p hp => by rw [if_neg (by omega)]),
    srs (N + 1) (b.val - 1) _ (fun p hp => by rw [if_neg (by omega)])]
  have hb := b.isLt
  simp only [κ1, if_true, one_ne_zero, if_false]
  rw [msq _ _ (by positivity), msq _ _ (by positivity)]
  by_cases h0 : b.val = 0
  · rw [h0]; simp; positivity
  · by_cases hN : b.val = N + 1
    · rw [hN]; simp; positivity
    · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega)]
      push_cast [Nat.cast_sub (show b.val ≤ N + 1 by omega), Nat.cast_sub (show 1 ≤ b.val by omega)]
      field_simp
      ring

lemma off01 (α a b d f t u : ℝ) (ht : t ≠ 0) (hu : u ≠ 0) (h : α * (a * a + f * f) = t * t) :
    α * (a / t * (b / t) * (a / u * (d / u)) + d / t * (f / t) * (b / u * (f / u))) =
      b / u * (d / u) := by
  have : α * (a / t * (b / t) * (a / u * (d / u)) + d / t * (f / t) * (b / u * (f / u))) =
      (α * (a * a + f * f)) * (b * d) / (t * t * (u * u)) := by field_simp <;> ring
  rw [this, h]; field_simp <;> ring

lemma off10 (α a b d f t u : ℝ) (ht : t ≠ 0) (hu : u ≠ 0) (h : α * (a * a + f * f) = t * t) :
    α * (b / t * (a / t) * (d / u * (a / u)) + f / t * (d / t) * (f / u * (b / u))) =
      d / u * (b / u) := by
  have : α * (b / t * (a / t) * (d / u * (a / u)) + f / t * (d / t) * (f / u * (b / u))) =
      (α * (a * a + f * f)) * (b * d) / (t * t * (u * u)) := by field_simp <;> ring
  rw [this, h]; field_simp <;> ring

lemma coef1 (N j j' k k' : ℕ) (hj : j < 2) (hj' : j' < 2) (hk : k < N + 1) (hk' : k' < N + 1) :
    (N + 1) / (N + 3) * ∑ p ∈ Finset.range (N + 1),
      ((if p + j = k + 0 ∧ p + j' = k' + 0 then
          κ1 N p j * κ1 N p j' * (u1 N k 0 * u1 N k' 0) else 0) +
       (if p + j = k + 1 ∧ p + j' = k' + 1 then
          κ1 N p j * κ1 N p j' * (u1 N k 1 * u1 N k' 1) else 0))
      + (if j = j' ∧ k = k' then 1 / ((N : ℝ) + 3) else 0) =
    if k + j' = k' + j then u1 N k j' * u1 N k' j else 0 := by
  rw [Finset.sum_add_distrib, srs (N + 1) (k - j) _ (fun p hp => by rw [if_neg (by omega)]),
    srs (N + 1) (k + 1 - j) _ (fun p hp => by rw [if_neg (by omega)])]
  have m1 : ∀ m : ℕ, _ := fun m => msq m ((N:ℝ)+1) (by positivity)
  have m2 : ∀ m : ℕ, _ := fun m => msq m ((N:ℝ)+2) (by positivity)
  have ht : Real.sqrt ((N:ℝ)+1) ≠ 0 := by positivity
  have hu : Real.sqrt ((N:ℝ)+2) ≠ 0 := by positivity
  have hsq : ∀ m : ℕ, Real.sqrt (m:ℝ) * Real.sqrt (m:ℝ) = m :=
    fun m => Real.mul_self_sqrt (Nat.cast_nonneg m)
  have htt : Real.sqrt ((N:ℝ)+1) * Real.sqrt ((N:ℝ)+1) = N + 1 :=
    Real.mul_self_sqrt (by positivity)
  interval_cases j <;> interval_cases j'
  · -- (0,0)
    by_cases hkk : k = k'
    · subst hkk
      simp only [κ1, u1, Nat.sub_zero, add_zero, and_self, if_true, one_ne_zero, if_false, m1, m2]
      rw [if_pos hk]
      split_ifs with h1
      · push_cast [Nat.cast_sub (show k ≤ N+1 by omega), Nat.cast_sub (show k ≤ N by omega)]
        field_simp; ring
      · obtain rfl : k = N := by omega
        simp; field_simp; ring
    · simp only [hkk, and_false, if_false, add_zero]
      split_ifs <;> first | omega | (simp at *; done) | simp
  · -- (0,1)
    by_cases hkk : k' = k + 1
    · subst hkk
      simp only [κ1, u1, Nat.add_sub_cancel, Nat.sub_zero, add_zero, eq_self_iff_true, and_self, true_and, and_true, false_and, and_false, if_true, if_false, one_ne_zero, zero_ne_one]
      rw [if_pos (by omega), if_pos (by omega)]
      exact off01 _ _ _ _ _ _ _ ht hu (by
        rw [hsq, hsq, htt]
        push_cast [Nat.cast_sub (show k ≤ N + 1 by omega)]
        field_simp; ring)
    · split_ifs <;> first | omega | (simp at *; done) | simp
  · -- (1,0)
    by_cases hkk : k = k' + 1
    · subst hkk
      simp only [κ1, u1, Nat.add_sub_cancel, Nat.sub_zero, add_zero, eq_self_iff_true, and_self, true_and, and_true, false_and, and_false, if_true, if_false, one_ne_zero, zero_ne_one]
      rw [if_pos (by omega), if_pos (by omega)]
      exact off10 _ _ _ _ _ _ _ ht hu (by
        rw [hsq, hsq, htt]
        push_cast [Nat.cast_sub (show k' ≤ N + 1 by omega)]
        field_simp; ring)
    · split_ifs <;> first | omega | (simp at *; done) | simp
  · -- (1,1)
    by_cases hkk : k = k'
    · subst hkk
      simp only [κ1, u1, Nat.sub_zero, add_zero, and_self, if_true, one_ne_zero, if_false, m1, m2]
      by_cases h0 : k = 0
      · subst h0
        simp
        field_simp; ring
      · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
          Nat.sub_add_cancel (by omega : 1 ≤ k), Nat.add_sub_cancel]
        push_cast [Nat.cast_sub (show k ≤ N + 1 by omega)]
        field_simp; ring
    · simp only [hkk, and_false, if_false, add_zero]
      split_ifs <;> first | omega | (simp at *; done) | simp

theorem fam1 (N : ℕ) : ConjugateDegradable (clonerDilation N (N + 1)) := by
  rw [dil_eq]
  have hE : N + 1 - N + 1 = 2 := by omega
  refine X7CF.main_cd (P := N + 1) (u1 N) (κ1 N) (Real.sqrt ((N + 1) / (N + 3)))
    (Real.sqrt (1 / (N + 3))) ?_ ?_ (hw1 N) (hK1 N) ?_ ?_
  · intro k i; have := k.isLt; have := i.isLt; omega
  · intro p j; have := p.isLt; have := j.isLt; omega
  · rw [Real.mul_self_sqrt (by positivity), Real.mul_self_sqrt (by positivity), hE]
    field_simp; ring
  · intro j j' k k'
    rw [Real.mul_self_sqrt (by positivity), Real.mul_self_sqrt (by positivity), hw1 N k, mul_one]
    rw [Finset.sum_congr rfl (fun p _ => sumE N (fun i =>
      if p.val + j.val = k.val + i ∧ p.val + j'.val = k'.val + i then
        κ1 N p.val j.val * κ1 N p.val j'.val * (u1 N k.val i * u1 N k'.val i) else 0))]
    rw [Fin.sum_univ_eq_sum_range (fun p =>
      (if p + j.val = k.val + 0 ∧ p + j'.val = k'.val + 0 then
        κ1 N p j.val * κ1 N p j'.val * (u1 N k.val 0 * u1 N k'.val 0) else 0) +
      (if p + j.val = k.val + 1 ∧ p + j'.val = k'.val + 1 then
        κ1 N p j.val * κ1 N p j'.val * (u1 N k.val 1 * u1 N k'.val 1) else 0))]
    simp only [Fin.ext_iff]
    exact coef1 N j j' k k' (by have := j.isLt; omega) (by have := j'.isLt; omega) k.isLt k'.isLt

end X7CF1

end QAlgorithms.Papers.Independent.Support50.P01

end


noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P01

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace X7CF2

open X7CF1 (msq srs off01 off10)

lemma cc0 (M i : ℕ) (hi : i < M) :
    cloningCoefficient 1 M 0 i = ((M - i : ℕ) : ℝ) / ((M : ℝ) * (M + 1) / 2) := by
  unfold cloningCoefficient
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
  rw [show n + 1 - 1 = n by omega, show n + 1 - 0 - i = (n - i) + 1 by omega,
    show n + 1 - i = (n - i) + 1 by omega, show n - i = (n - i) by rfl,
    show 1 - 0 = 1 by rfl, zero_add, Nat.factorial_succ (n - i),
    show n + 1 + 1 = (n + 1) + 1 by rfl, Nat.factorial_succ (n + 1), Nat.factorial_succ n]
  have : (i.factorial : ℝ) ≠ 0 := by positivity
  have : ((n - i).factorial : ℝ) ≠ 0 := by positivity
  have : ((n).factorial : ℝ) ≠ 0 := by positivity
  simp only [Nat.factorial_one, Nat.factorial_zero, Nat.factorial_two]
  push_cast
  field_simp
  ring

lemma cc1 (M i : ℕ) (hi : i < M) :
    cloningCoefficient 1 M 1 i = ((i + 1 : ℕ) : ℝ) / ((M : ℝ) * (M + 1) / 2) := by
  unfold cloningCoefficient
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
  rw [show n + 1 - 1 = n by omega,
    show 1 - 1 = 0 by rfl, add_comm 1 i, Nat.factorial_succ i,
    show n + 1 + 1 = (n + 1) + 1 by rfl, Nat.factorial_succ (n + 1), Nat.factorial_succ n]
  have : (i.factorial : ℝ) ≠ 0 := by positivity
  have : ((n - i).factorial : ℝ) ≠ 0 := by positivity
  have : ((n).factorial : ℝ) ≠ 0 := by positivity
  simp only [Nat.factorial_one, Nat.factorial_zero, Nat.factorial_two]
  push_cast
  field_simp
  ring

/-- Atom-form amplitudes of the `(1, M)` cloner. -/
def u2 (M : ℕ) : ℕ → ℕ → ℝ := fun k i =>
  if k = 0 then Real.sqrt ((M - i : ℕ) : ℝ) / Real.sqrt ((M : ℝ) * (M + 1) / 2)
  else Real.sqrt ((i + 1 : ℕ) : ℝ) / Real.sqrt ((M : ℝ) * (M + 1) / 2)

/-- Kraus amplitudes of the symmetric one-qubit partial trace `Sym^M → Sym^{M-1}`. -/
def κ2 (M : ℕ) : ℕ → ℕ → ℝ := fun p j =>
  if p = 0 then Real.sqrt ((M - j : ℕ) : ℝ) / Real.sqrt (M : ℝ)
  else Real.sqrt ((j + 1 : ℕ) : ℝ) / Real.sqrt (M : ℝ)

lemma sumI (M : ℕ) (hM : 1 ≤ M) (f : ℕ → ℝ) :
    ∑ i : Fin (M - 1 + 1), f i.val = ∑ i ∈ Finset.range M, f i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => f i), show M - 1 + 1 = M by omega]

lemma dil_eq (M : ℕ) (hM : 1 ≤ M) : clonerDilation 1 M = X7CF.shiftU (u2 M) := by
  ext ⟨b, i⟩ k
  simp only [clonerDilation, X7CF.shiftU]
  split_ifs with h
  · congr 1
    have hi := i.isLt
    have hk := k.isLt
    rcases (show k.val = 0 ∨ k.val = 1 by omega) with hk0 | hk1
    · rw [hk0, cc0 M i (by omega), Real.sqrt_div' _ (by positivity)]
      simp [u2]
    · rw [hk1, cc1 M i (by omega), Real.sqrt_div' _ (by positivity)]
      simp [u2]
  · rfl

lemma gauss (M : ℕ) : ∑ i ∈ Finset.range M, ((i + 1 : ℕ) : ℝ) = M * (M + 1) / 2 := by
  induction M with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma gauss' (M : ℕ) : ∑ i ∈ Finset.range M, ((M - i : ℕ) : ℝ) = M * (M + 1) / 2 := by
  rw [← gauss M, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  simp only [Finset.mem_range] at hi
  congr 2; omega

lemma hw2 (M : ℕ) (hM : 1 ≤ M) (k : Fin (1 + 1)) :
    ∑ i : Fin (M - 1 + 1), u2 M k.val i.val * u2 M k.val i.val = 1 := by
  rw [sumI M hM (fun i => u2 M k.val i * u2 M k.val i)]
  have hq : (0:ℝ) < (M : ℝ) * (M + 1) / 2 := by
    have : (1:ℝ) ≤ M := by exact_mod_cast hM
    positivity
  rcases (show k.val = 0 ∨ k.val = 1 by omega) with hk | hk
  · simp only [hk, u2, if_true]
    simp only [msq _ _ hq, ← Finset.sum_div, gauss']
    field_simp
  · simp only [hk, u2, one_ne_zero, if_false]
    simp only [msq _ _ hq, ← Finset.sum_div, gauss]
    field_simp

lemma hK2 (M : ℕ) (hM : 1 ≤ M) (b : Fin (M + 1)) :
    ∑ p : Fin (1 + 1), ∑ j : Fin (M - 1 + 1),
      (if b.val = p.val + j.val then κ2 M p j * κ2 M p j else 0) = 1 := by
  rw [Fin.sum_univ_two]
  rw [sumI M hM (fun j => if b.val = (0 : Fin (1+1)).val + j then
      κ2 M (0 : Fin (1+1)).val j * κ2 M (0 : Fin (1+1)).val j else 0),
    sumI M hM (fun j => if b.val = (1 : Fin (1+1)).val + j then
      κ2 M (1 : Fin (1+1)).val j * κ2 M (1 : Fin (1+1)).val j else 0)]
  simp only [Fin.val_zero, Fin.val_one, zero_add]
  rw [srs M b.val _ (fun p hp => by rw [if_neg (by omega)]),
    srs M (b.val - 1) _ (fun p hp => by rw [if_neg (by omega)])]
  have hb := b.isLt
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  simp only [κ2, if_true, one_ne_zero, if_false]
  rw [msq _ _ hM', msq _ _ hM']
  by_cases h0 : b.val = 0
  · rw [h0]; simp; rw [if_pos (by omega)]; field_simp
  · by_cases hN : b.val = M
    · rw [hN]; simp
      rw [if_pos (by omega), if_pos (by omega)]
      push_cast [Nat.cast_sub hM]; field_simp; ring
    · rw [if_pos (show b.val < M by omega), if_pos (show b.val - 1 < M by omega),
        if_pos (show b.val = 1 + (b.val - 1) by omega), Nat.sub_add_cancel (by omega : 1 ≤ b.val)]
      push_cast [Nat.cast_sub (show b.val ≤ M by omega), Nat.cast_sub (show 1 ≤ b.val by omega)]
      field_simp
      ring

lemma off2a (α a b d f r q : ℝ) (hr : r ≠ 0) (hq : q ≠ 0) (h : α * (a * a + f * f) = r * r) :
    α * (a / r * (d / r) * (a / q * (b / q)) + b / r * (f / r) * (d / q * (f / q))) =
      d / q * (b / q) := by
  have : α * (a / r * (d / r) * (a / q * (b / q)) + b / r * (f / r) * (d / q * (f / q))) =
      (α * (a * a + f * f)) * (b * d) / (r * r * (q * q)) := by field_simp <;> ring
  rw [this, h]; field_simp <;> ring

lemma off2b (α a b d f r q : ℝ) (hr : r ≠ 0) (hq : q ≠ 0) (h : α * (a * a + f * f) = r * r) :
    α * (d / r * (a / r) * (b / q * (a / q)) + f / r * (b / r) * (f / q * (d / q))) =
      b / q * (d / q) := by
  have : α * (d / r * (a / r) * (b / q * (a / q)) + f / r * (b / r) * (f / q * (d / q))) =
      (α * (a * a + f * f)) * (b * d) / (r * r * (q * q)) := by field_simp <;> ring
  rw [this, h]; field_simp <;> ring

lemma coef2 (M j j' k k' : ℕ) (hM : 1 ≤ M) (hj : j < M) (hj' : j' < M) (hk : k < 2) (hk' : k' < 2) :
    M / (M + 2) * (∑ i ∈ Finset.range M,
      (if 0 + j = k + i ∧ 0 + j' = k' + i then
          κ2 M 0 j * κ2 M 0 j' * (u2 M k i * u2 M k' i) else 0) +
      ∑ i ∈ Finset.range M,
      (if 1 + j = k + i ∧ 1 + j' = k' + i then
          κ2 M 1 j * κ2 M 1 j' * (u2 M k i * u2 M k' i) else 0))
      + (if j = j' ∧ k = k' then 2 / ((M : ℝ) * (M + 2)) else 0) =
    if k + j' = k' + j then u2 M k j' * u2 M k' j else 0 := by
  rw [srs M (j - k) _ (fun p hp => by rw [if_neg (by omega)]),
    srs M (1 + j - k) _ (fun p hp => by rw [if_neg (by omega)])]
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  have hQ : (0:ℝ) < (M : ℝ) * (M + 1) / 2 := by positivity
  have m1 : ∀ m : ℕ, _ := fun m => msq m (M : ℝ) hM'
  have m2 : ∀ m : ℕ, _ := fun m => msq m ((M : ℝ) * (M + 1) / 2) hQ
  have hr : Real.sqrt (M : ℝ) ≠ 0 := by positivity
  have hq : Real.sqrt ((M : ℝ) * (M + 1) / 2) ≠ 0 := by positivity
  have hsq : ∀ m : ℕ, Real.sqrt (m:ℝ) * Real.sqrt (m:ℝ) = m :=
    fun m => Real.mul_self_sqrt (Nat.cast_nonneg m)
  interval_cases k <;> interval_cases k'
  · -- (0,0)
    by_cases hjj : j = j'
    · subst hjj
      simp only [κ2, u2, Nat.add_sub_cancel, Nat.add_sub_cancel_left, Nat.sub_zero, zero_add, add_zero, and_self, true_and, false_and, if_true, if_false, one_ne_zero, zero_ne_one]
      simp only [m1, m2]
      rw [if_pos (show j < M by omega)]
      split_ifs with h1
      · push_cast [Nat.cast_sub (show j ≤ M by omega), Nat.cast_sub (show 1 + j ≤ M by omega)]
        field_simp; ring
      · obtain rfl : M = j + 1 := by omega
        simp; field_simp; ring
    · simp only [hjj, false_and, if_false, add_zero]
      split_ifs <;> first | omega | (simp at *; done) | simp
  · -- (0,1)
    by_cases hjj : j' = j + 1
    · subst hjj
      simp only [κ2, u2, Nat.add_sub_cancel, Nat.add_sub_cancel_left, Nat.sub_zero, zero_add, add_zero, and_self, true_and, false_and, if_true, if_false, one_ne_zero, zero_ne_one]
      simp only [add_comm 1 j, ite_true, if_pos hj, if_pos hj', and_false, ite_false, add_zero]
      exact off2a _ _ _ _ _ _ _ hr hq (by
        rw [hsq, hsq, Real.mul_self_sqrt hM'.le]
        push_cast [Nat.cast_sub (show j ≤ M by omega)]
        field_simp; ring)
    · split_ifs <;> first | omega | (simp at *; done) | simp
  · -- (1,0)
    by_cases hjj : j = j' + 1
    · subst hjj
      simp only [κ2, u2, Nat.add_sub_cancel, Nat.add_sub_cancel_left, Nat.sub_zero, zero_add, add_zero, and_self, true_and, false_and, if_true, if_false, one_ne_zero, zero_ne_one]
      simp only [add_comm 1 j', ite_true, if_pos hj, if_pos hj', and_false, ite_false, add_zero]
      exact off2b _ _ _ _ _ _ _ hr hq (by
        rw [hsq, hsq, Real.mul_self_sqrt hM'.le]
        push_cast [Nat.cast_sub (show j' ≤ M by omega)]
        field_simp; ring)
    · split_ifs <;> first | omega | (simp at *; done) | simp
  · -- (1,1)
    by_cases hjj : j = j'
    · subst hjj
      simp only [κ2, u2, Nat.add_sub_cancel, Nat.add_sub_cancel_left, Nat.sub_zero, zero_add, add_zero, and_self, true_and, false_and, if_true, if_false, one_ne_zero, zero_ne_one]
      simp only [m1, m2]
      by_cases h0 : j = 0
      · subst h0
        simp [hj]
        field_simp; ring
      · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
          Nat.sub_add_cancel (by omega : 1 ≤ j)]
        push_cast [Nat.cast_sub (show j ≤ M by omega)]
        field_simp; ring
    · simp only [hjj, false_and, if_false, add_zero]
      split_ifs <;> first | omega | (simp at *; done) | simp

theorem fam2 (M : ℕ) (hM : 1 ≤ M) : ConjugateDegradable (clonerDilation 1 M) := by
  rw [dil_eq M hM]
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  refine X7CF.main_cd (P := 1 + 1) (u2 M) (κ2 M) (Real.sqrt (M / (M + 2)))
    (Real.sqrt (2 / (M * (M + 2)))) ?_ ?_ (hw2 M hM) (hK2 M hM) ?_ ?_
  · intro k i; have := k.isLt; have := i.isLt; omega
  · intro p j; have := p.isLt; have := j.isLt; omega
  · rw [Real.mul_self_sqrt (by positivity), Real.mul_self_sqrt (by positivity),
      Nat.sub_add_cancel hM]
    field_simp
  · intro j j' k k'
    rw [Real.mul_self_sqrt (by positivity), Real.mul_self_sqrt (by positivity), hw2 M hM k, mul_one]
    rw [Fin.sum_univ_two]
    rw [sumI M hM (fun i =>
      if (0 : Fin (1 + 1)).val + j.val = k.val + i ∧ (0 : Fin (1 + 1)).val + j'.val = k'.val + i then
        κ2 M (0 : Fin (1 + 1)).val j.val * κ2 M (0 : Fin (1 + 1)).val j'.val *
          (u2 M k.val i * u2 M k'.val i) else 0),
      sumI M hM (fun i =>
      if (1 : Fin (1 + 1)).val + j.val = k.val + i ∧ (1 : Fin (1 + 1)).val + j'.val = k'.val + i then
        κ2 M (1 : Fin (1 + 1)).val j.val * κ2 M (1 : Fin (1 + 1)).val j'.val *
          (u2 M k.val i * u2 M k'.val i) else 0)]
    simp only [Fin.val_zero, Fin.val_one, Fin.ext_iff]
    exact coef2 M j j' k k' hM (by have := j.isLt; omega) (by have := j'.isLt; omega)
      k.isLt k'.isLt

/-- PDF pp.8–10, Theorem 1: both cloning families are conjugate degradable. -/
theorem main :
    (∀ N : ℕ, 1 ≤ N → ConjugateDegradable (clonerDilation N (N + 1))) ∧
    (∀ M : ℕ, 1 ≤ M → ConjugateDegradable (clonerDilation 1 M)) :=
  ⟨fun N _ => X7CF1.fam1 N, fun M hM => fam2 M hM⟩

end X7CF2

end QAlgorithms.Papers.Independent.Support50.P01

end

section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P01 in
theorem solution :
    (∀ N : ℕ, 1≤N → ConjugateDegradable (clonerDilation N (N+1))) ∧
    (∀ M : ℕ, 1≤M → ConjugateDegradable (clonerDilation 1 M)) :=
  QAlgorithms.Papers.Independent.Support50.P01.X7CF2.main

end
