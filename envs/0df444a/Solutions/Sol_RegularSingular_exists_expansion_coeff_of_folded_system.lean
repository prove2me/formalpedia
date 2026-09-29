-- Prove2me | solution 1 for RegularSingular.exists_expansion_coeff_of_folded_system
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/234cb7a3-3f01-5351-ba9c-576966067409

import Mathlib
import Theorems.Thm_RegularSingular_exists_logDepth_le_natDegree_norm_sub_expansion_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RegularSingular_exists_expansion_coeff_of_folded_system

open scoped BigOperators
open Polynomial

noncomputable section

namespace RegSingFolded

section Algebra

variable {K : Type*} [Field K]
variable {m β : Type*} [Fintype m] [DecidableEq m] [Fintype β] [DecidableEq β]
variable (σ : m → β) (rel : β → β → Prop)

def Lower (X : Matrix m m K) : Prop := ∀ ⦃s t : m⦄, ¬ rel (σ t) (σ s) → X s t = 0

def SameDiag (X X' : Matrix m m K) : Prop := ∀ ⦃s t : m⦄, σ s = σ t → X s t = X' s t

structure Adm (X X' : Matrix m m K) : Prop where
  lowerL : Lower σ rel X
  lowerR : Lower σ rel X'
  sd : SameDiag σ X X'

def StrictLower (X : Matrix m m K) : Prop :=
  ∀ ⦃s t : m⦄, ¬ (rel (σ t) (σ s) ∧ σ t ≠ σ s) → X s t = 0

open Classical in

noncomputable def height (s : m) : ℕ :=
  (Finset.univ.filter fun b : β => rel b (σ s) ∧ b ≠ σ s).card

variable {σ rel}

theorem lower_zero : Lower σ rel (0 : Matrix m m K) := fun _ _ _ => rfl

theorem lower_one (hrefl : ∀ b, rel b b) : Lower σ rel (1 : Matrix m m K) := by
  intro s t h
  have hst : s ≠ t := by
    rintro rfl
    exact h (hrefl _)
  exact Matrix.one_apply_ne hst

theorem lower_add {X Y : Matrix m m K} (hX : Lower σ rel X) (hY : Lower σ rel Y) :
    Lower σ rel (X + Y) := by
  intro s t h
  simp [Matrix.add_apply, hX h, hY h]

theorem lower_smul {X : Matrix m m K} (hX : Lower σ rel X) (c : K) : Lower σ rel (c • X) := by
  intro s t h
  simp [Matrix.smul_apply, hX h]

theorem mul_entry_eq_zero (htrans : ∀ a b c, rel a b → rel b c → rel a c)
    {X Y : Matrix m m K} (hX : Lower σ rel X) (hY : Lower σ rel Y)
    {s w t : m} (h : ¬ rel (σ t) (σ s)) : X s w * Y w t = 0 := by
  by_cases h1 : rel (σ w) (σ s)
  · have h2 : ¬ rel (σ t) (σ w) := fun h2 => h (htrans _ _ _ h2 h1)
    rw [hY h2, mul_zero]
  · rw [hX h1, zero_mul]

theorem lower_mul (htrans : ∀ a b c, rel a b → rel b c → rel a c)
    {X Y : Matrix m m K} (hX : Lower σ rel X) (hY : Lower σ rel Y) : Lower σ rel (X * Y) := by
  intro s t h
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun w _ => mul_entry_eq_zero htrans hX hY h

theorem sameDiag_mul (htrans : ∀ a b c, rel a b → rel b c → rel a c)
    (hanti : ∀ a b, rel a b → rel b a → a = b) {X Y X' Y' : Matrix m m K}
    (hX : Lower σ rel X) (hY : Lower σ rel Y) (hX' : Lower σ rel X') (hY' : Lower σ rel Y')
    (hXX' : SameDiag σ X X') (hYY' : SameDiag σ Y Y') : SameDiag σ (X * Y) (X' * Y') := by
  intro s t hst
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : σ s = σ w
  · rw [hXX' hw, hYY' (hw.symm.trans hst)]
  · have key : ∀ {X₁ Y₁ : Matrix m m K}, Lower σ rel X₁ → Lower σ rel Y₁ → X₁ s w * Y₁ w t = 0 := by
      intro X₁ Y₁ hX₁ hY₁
      by_cases h1 : rel (σ w) (σ s)
      · by_cases h2 : rel (σ t) (σ w)
        · rw [← hst] at h2
          exact absurd (hanti _ _ h2 h1) hw
        · rw [hY₁ h2, mul_zero]
      · rw [hX₁ h1, zero_mul]
    rw [key hX hY, key hX' hY']

theorem adm_one (hrefl : ∀ b, rel b b) : Adm σ rel (1 : Matrix m m K) 1 :=
  ⟨lower_one hrefl, lower_one hrefl, fun _ _ _ => rfl⟩

theorem adm_zero : Adm σ rel (0 : Matrix m m K) 0 :=
  ⟨lower_zero, lower_zero, fun _ _ _ => rfl⟩

theorem adm_add {X X' Y Y' : Matrix m m K} (h1 : Adm σ rel X X') (h2 : Adm σ rel Y Y') :
    Adm σ rel (X + Y) (X' + Y') :=
  ⟨lower_add h1.lowerL h2.lowerL, lower_add h1.lowerR h2.lowerR, fun s t hst => by
    simp [Matrix.add_apply, h1.sd hst, h2.sd hst]⟩

theorem adm_smul {X X' : Matrix m m K} (h : Adm σ rel X X') (c : K) :
    Adm σ rel (c • X) (c • X') :=
  ⟨lower_smul h.lowerL c, lower_smul h.lowerR c, fun s t hst => by
    simp [Matrix.smul_apply, h.sd hst]⟩

theorem adm_mul (htrans : ∀ a b c, rel a b → rel b c → rel a c)
    (hanti : ∀ a b, rel a b → rel b a → a = b) {X X' Y Y' : Matrix m m K}
    (h1 : Adm σ rel X X') (h2 : Adm σ rel Y Y') : Adm σ rel (X * Y) (X' * Y') :=
  ⟨lower_mul htrans h1.lowerL h2.lowerL, lower_mul htrans h1.lowerR h2.lowerR,
    sameDiag_mul htrans hanti h1.lowerL h2.lowerL h1.lowerR h2.lowerR h1.sd h2.sd⟩

theorem adm_pow (hrefl : ∀ b, rel b b) (htrans : ∀ a b c, rel a b → rel b c → rel a c)
    (hanti : ∀ a b, rel a b → rel b a → a = b) {X X' : Matrix m m K}
    (h : Adm σ rel X X') (k : ℕ) : Adm σ rel (X ^ k) (X' ^ k) := by
  induction k with
  | zero => simpa using adm_one hrefl
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact adm_mul htrans hanti ih h

theorem adm_sum {ι' : Type*} (s : Finset ι') (f g : ι' → Matrix m m K)
    (h : ∀ i ∈ s, Adm σ rel (f i) (g i)) :
    Adm σ rel (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using adm_zero
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact adm_add (h a (Finset.mem_cons.2 (Or.inl rfl)))
      (ih fun i hi => h i (Finset.mem_cons.2 (Or.inr hi)))

theorem adm_aeval (hrefl : ∀ b, rel b b) (htrans : ∀ a b c, rel a b → rel b c → rel a c)
    (hanti : ∀ a b, rel a b → rel b a → a = b) {X X' : Matrix m m K}
    (h : Adm σ rel X X') (q : K[X]) : Adm σ rel (aeval X q) (aeval X' q) := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range]
  exact adm_sum _ _ _ fun i _ => adm_smul (adm_pow hrefl htrans hanti h i) _

theorem strictLower_of_lower_of_diag {X : Matrix m m K} (hX : Lower σ rel X)
    (hd : ∀ ⦃s t : m⦄, σ s = σ t → X s t = 0) : StrictLower σ rel X := by
  intro s t h
  by_cases hst : σ t = σ s
  · exact hd hst.symm
  · exact hX fun hr => h ⟨hr, hst⟩

theorem height_lt_of_rel (htrans : ∀ a b c, rel a b → rel b c → rel a c)
    (hanti : ∀ a b, rel a b → rel b a → a = b) {t w : m}
    (h : rel (σ t) (σ w) ∧ σ t ≠ σ w) : height σ rel t < height σ rel w := by
  classical
  unfold height
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset ?_).2 ⟨σ t, ?_, ?_⟩)
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    refine ⟨htrans _ _ _ hb.1 h.1, ?_⟩
    rintro rfl
    exact h.2 (hanti _ _ h.1 hb.1)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  · simp

theorem height_lt_card (s : m) : height σ rel s < Fintype.card β := by
  classical
  unfold height
  rw [← Finset.card_univ]
  apply Finset.card_lt_card
  rw [Finset.filter_ssubset]
  exact ⟨σ s, Finset.mem_univ _, by simp⟩

theorem pow_apply_ne_zero (htrans : ∀ a b c, rel a b → rel b c → rel a c)
    (hanti : ∀ a b, rel a b → rel b a → a = b) {X : Matrix m m K}
    (hX : StrictLower σ rel X) :
    ∀ k : ℕ, ∀ s t : m, (X ^ k) s t ≠ 0 → k + height σ rel t ≤ height σ rel s := by
  intro k
  induction k with
  | zero =>
    intro s t h
    by_cases hst : s = t
    · subst hst
      simp
    · exact absurd (by rw [pow_zero]; exact Matrix.one_apply_ne hst) h
  | succ k ih =>
    intro s t h
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 : (X ^ k) s w ≠ 0 := left_ne_zero_of_mul hw
    have h2 : X w t ≠ 0 := right_ne_zero_of_mul hw
    have h3 : rel (σ t) (σ w) ∧ σ t ≠ σ w := by
      by_contra hc
      exact h2 (hX hc)
    have h4 := ih s w h1
    have h5 := height_lt_of_rel htrans hanti h3
    omega

theorem pow_card_eq_zero (htrans : ∀ a b c, rel a b → rel b c → rel a c)
    (hanti : ∀ a b, rel a b → rel b a → a = b) {X : Matrix m m K}
    (hX : StrictLower σ rel X) : X ^ Fintype.card β = 0 := by
  ext s t
  by_contra h
  have h1 := pow_apply_ne_zero htrans hanti hX _ s t h
  have h2 := height_lt_card (σ := σ) (rel := rel) s
  omega

theorem aeval_pow_card_eq_zero (hrefl : ∀ b, rel b b)
    (htrans : ∀ a b c, rel a b → rel b c → rel a c)
    (hanti : ∀ a b, rel a b → rel b a → a = b) {X X' : Matrix m m K} (h : Adm σ rel X X')
    (q : K[X]) (hq : aeval X' q = 0) : aeval X (q ^ Fintype.card β) = 0 := by
  have hadm := adm_aeval hrefl htrans hanti h q
  rw [map_pow]
  apply pow_card_eq_zero htrans hanti
  refine strictLower_of_lower_of_diag hadm.lowerL ?_
  intro s t hst
  rw [hadm.sd hst, hq]
  rfl

variable {α γ : Type*} [Fintype α] [DecidableEq α] [Fintype γ] [DecidableEq γ]

def blkFun (ε : α × γ ≃ m) (X : Matrix α α K) : Matrix m m K :=
  Matrix.of fun s t => if (ε.symm s).2 = (ε.symm t).2 then X (ε.symm s).1 (ε.symm t).1 else 0

def blkLin (ε : α × γ ≃ m) : Matrix α α K →ₗ[K] Matrix m m K where
  toFun := blkFun ε
  map_add' X Y := by
    ext s t
    simp only [blkFun, Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp
  map_smul' c X := by
    ext s t
    simp only [blkFun, Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

theorem blkLin_apply (ε : α × γ ≃ m) (X : Matrix α α K) (s t : m) :
    blkLin ε X s t = if (ε.symm s).2 = (ε.symm t).2 then X (ε.symm s).1 (ε.symm t).1 else 0 :=
  rfl

theorem blkLin_one (ε : α × γ ≃ m) : blkLin ε (1 : Matrix α α K) = 1 := by
  ext s t
  rw [blkLin_apply]
  by_cases hst : s = t
  · subst hst
    simp
  · rw [Matrix.one_apply_ne hst]
    split_ifs with h2
    · rw [Matrix.one_apply_ne]
      intro h1
      exact hst (ε.symm.injective (Prod.ext h1 h2))
    · rfl

theorem blkLin_mul (ε : α × γ ≃ m) (X Y : Matrix α α K) :
    blkLin ε (X * Y) = blkLin ε X * blkLin ε Y := by
  ext s t
  rw [Matrix.mul_apply, blkLin_apply]
  simp only [blkLin_apply, Matrix.mul_apply]
  rw [← Equiv.sum_comp ε]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  by_cases h : (ε.symm s).2 = (ε.symm t).2
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single (ε.symm t).2]
    · simp [h]
    · intro c _ hc
      simp [hc]
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  · rw [if_neg h]
    symm
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => ?_
    by_cases h1 : (ε.symm s).2 = c
    · have h2 : ¬ c = (ε.symm t).2 := fun h2 => h (h1.trans h2)
      simp [h2]
    · simp [h1]

def blkAlgHom (ε : α × γ ≃ m) : Matrix α α K →ₐ[K] Matrix m m K :=
  AlgHom.ofLinearMap (blkLin ε) (blkLin_one ε) (blkLin_mul ε)

theorem blkAlgHom_apply (ε : α × γ ≃ m) (X : Matrix α α K) (s t : m) :
    blkAlgHom ε X s t =
      if (ε.symm s).2 = (ε.symm t).2 then X (ε.symm s).1 (ε.symm t).1 else 0 :=
  rfl

end Algebra

universe uP

theorem expansion_fintype {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Type uP}
    [TopologicalSpace P] (q : ℂ[X]) (hq : q ≠ 0) (d : ℕ) (L m ρ θ : ℝ)
    (hθ : ∀ e : ℂ, q.IsRoot e → ∀ n : ℕ, ρ < (e + n).re → θ < (e + n).re)
    (M : P → Matrix ι ι ℂ) (A : P → Fin d → ((ι → ℂ) →L[ℂ] (ι → ℂ)))
    (hM : Continuous M) (hML : ∀ p i j, ‖M p i j‖ ≤ L) (hMq : ∀ p, aeval (M p) q = 0)
    (hA : ∀ k, Continuous fun p => A p k) (hAL : ∀ p k, ‖A p k‖ ≤ L)
    (F F' : P → ℝ → (ι → ℂ)) (B : P → ℝ)
    (hF : ContinuousOn (fun w : P × ℝ => F w.1 w.2) (Set.univ ×ˢ Set.Ioc 0 1))
    (hB : ∀ p₀ : P, ∃ B₀ : ℝ, ∀ᶠ p in nhds p₀, B p ≤ B₀)
    (hsys : ∀ p, ∀ y ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt (F p) (F' p y) y ∧
      (y : ℂ) • F' p y =
        (fun i => ∑ j, M p i j • F p y j) + ∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • A p k (F p y))
    (hbd : ∀ p, ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖F p y‖ ≤ B p * y ^ (-m)) :
    ∃ (D : ℕ) (S : Finset ℂ) (κ : ℝ), D ≤ q.natDegree ∧
      (∀ μ ∈ S, μ.re ≤ ρ ∧ ∃ (e : ℂ) (n : ℕ), q.IsRoot e ∧ μ = e + n) ∧
      ∃ c : ℂ → ℕ → P → (ι → ℂ),
        (∀ μ j, Continuous (c μ j)) ∧
        ∀ p, (∀ μ j, ‖c μ j p‖ ≤ κ * B p) ∧
          ∀ y ∈ Set.Ioc (0 : ℝ) 1,
            ‖F p y - ∑ μ ∈ S, ∑ j ∈ Finset.range D,
                ((y : ℂ) ^ μ * ((Real.log y : ℝ) : ℂ) ^ j) • c μ j p‖ ≤ κ * B p * y ^ θ := by
  obtain ⟨D, hD, H⟩ :=
    RegularSingular.exists_logDepth_le_natDegree_norm_sub_expansion_le.{0, uP} q hq
  set r : ℕ := Fintype.card ι with hr
  obtain ⟨S, κ, hS, H2⟩ := H ℂ r d L m ρ θ hθ
  let ε : ι ≃ Fin r := Fintype.equivFin ι

  let Ψ : (ι → ℂ) →L[ℂ] (Fin r → ℂ) :=
    ContinuousLinearMap.pi fun s => ContinuousLinearMap.proj (ε.symm s)
  let Ψ' : (Fin r → ℂ) →L[ℂ] (ι → ℂ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (ε i)
  have hΨ : ∀ x s, Ψ x s = x (ε.symm s) := fun x s => rfl
  have hΨ' : ∀ x i, Ψ' x i = x (ε i) := fun x i => rfl
  have nΨ : ∀ x, ‖Ψ x‖ ≤ ‖x‖ := fun x =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun s => by
      rw [hΨ]; exact norm_le_pi_norm x _
  have nΨ' : ∀ x, ‖Ψ' x‖ ≤ ‖x‖ := fun x =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun i => by
      rw [hΨ']; exact norm_le_pi_norm x _

  let Mt : P → Matrix (Fin r) (Fin r) ℂ := fun p => Matrix.of fun s t => M p (ε.symm s) (ε.symm t)
  let At : P → Fin d → ((Fin r → ℂ) →L[ℂ] (Fin r → ℂ)) := fun p k => Ψ.comp ((A p k).comp Ψ')
  let Ft : P → ℝ → (Fin r → ℂ) := fun p y s => F p y (ε.symm s)
  let F't : P → ℝ → (Fin r → ℂ) := fun p y s => F' p y (ε.symm s)
  have hΨ'F : ∀ p y, Ψ' (Ft p y) = F p y := by
    intro p y
    funext i
    rw [hΨ']
    show F p y (ε.symm (ε i)) = F p y i
    rw [Equiv.symm_apply_apply]
  have hMt : Continuous Mt := continuous_matrix fun s t => hM.matrix_elem (ε.symm s) (ε.symm t)
  have hMtL : ∀ p s t, ‖Mt p s t‖ ≤ L := fun p s t => hML p _ _
  have hMtq : ∀ p, aeval (Mt p) q = 0 := by
    intro p
    have : Mt p = Matrix.reindexAlgEquiv ℂ ℂ ε (M p) := by
      ext s t
      simp [Mt, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [this, aeval_algHom_apply, hMq p, map_zero]
  have hAt : ∀ k, Continuous fun p => At p k := fun k =>
    continuous_const.clm_comp ((hA k).clm_comp continuous_const)
  have hAtL : ∀ p k, ‖At p k‖ ≤ L := by
    intro p k
    have hL : 0 ≤ L := (norm_nonneg _).trans (hAL p k)
    refine ContinuousLinearMap.opNorm_le_bound _ hL fun x => ?_
    calc ‖At p k x‖ = ‖Ψ (A p k (Ψ' x))‖ := rfl
      _ ≤ ‖A p k (Ψ' x)‖ := nΨ _
      _ ≤ ‖A p k‖ * ‖Ψ' x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ L * ‖x‖ := mul_le_mul (hAL p k) (nΨ' x) (norm_nonneg _) hL
  have hFt : ContinuousOn (fun w : P × ℝ => Ft w.1 w.2) (Set.univ ×ˢ Set.Ioc 0 1) :=
    continuousOn_pi.2 fun s => (continuous_apply (ε.symm s)).comp_continuousOn hF
  have hsyst : ∀ p, ∀ y ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt (Ft p) (F't p y) y ∧
      (y : ℂ) • F't p y =
        (fun s => ∑ t, Mt p s t • Ft p y t) +
          ∑ k : Fin d, ((y : ℂ) ^ ((k : ℕ) + 1)) • At p k (Ft p y) := by
    intro p y hy
    obtain ⟨hd, heq⟩ := hsys p y hy
    refine ⟨hasDerivAt_pi.2 fun s => (hasDerivAt_pi.1 hd) (ε.symm s), ?_⟩
    funext s
    have h1 := congrFun heq (ε.symm s)
    simp only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul] at h1
    simp only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul]
    have h2 : (∑ t, Mt p s t * Ft p y t) = ∑ j, M p (ε.symm s) j * F p y j :=
      Equiv.sum_comp ε.symm (fun j => M p (ε.symm s) j * F p y j)
    have h3 : ∀ k, (At p k) (Ft p y) s = (A p k) (F p y) (ε.symm s) := by
      intro k
      show (Ψ (A p k (Ψ' (Ft p y)))) s = _
      rw [hΨ'F, hΨ]
    rw [h2]
    simp only [h3]
    exact h1
  have hbdt : ∀ p, ∀ y ∈ Set.Ioc (0 : ℝ) 1, ‖Ft p y‖ ≤ B p * y ^ (-m) := fun p y hy =>
    (nΨ (F p y)).trans (hbd p y hy)
  obtain ⟨c, hc, hcp⟩ := H2 P Mt At hMt hMtL hMtq hAt hAtL Ft F't B hFt hB hsyst hbdt
  refine ⟨D, S, κ, hD, hS, fun μ j p i => c μ j p (ε i), fun μ j => ?_, fun p => ⟨fun μ j => ?_, ?_⟩⟩
  · exact continuous_pi fun i => (continuous_apply (ε i)).comp (hc μ j)
  · exact ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
      norm_le_pi_norm (c μ j p) (ε i)).trans ((hcp p).1 μ j)
  · intro y hy
    refine le_trans ?_ ((hcp p).2.2 y hy)
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    have : (F p y - ∑ μ ∈ S, ∑ j ∈ Finset.range D,
          ((y : ℂ) ^ μ * ((Real.log y : ℝ) : ℂ) ^ j) • fun i => c μ j p (ε i)) i =
        (Ft p y - ∑ μ ∈ S, ∑ j ∈ Finset.range D,
          ((y : ℂ) ^ μ * ((Real.log y : ℝ) : ℂ) ^ j) • c μ j p) (ε i) := by
      simp only [Ft, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, Equiv.symm_apply_apply]
    rw [this]
    exact norm_le_pi_norm _ _

section Flatten

variable {n J R d₂ d : ℕ} {P : Type*}

abbrev Idx (n J R : ℕ) := Fin R × (Fin n × Fin J)

def Rel (e : Fin n → ℂ) (i' i : Fin n) : Prop := ∃ a : ℕ, e i' + (a : ℂ) = e i

theorem rel_refl (e : Fin n → ℂ) (i : Fin n) : Rel e i i := ⟨0, by simp⟩

theorem rel_trans (e : Fin n → ℂ) (a b c : Fin n) (h1 : Rel e a b) (h2 : Rel e b c) :
    Rel e a c := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := h2
  exact ⟨k + l, by push_cast; rw [← hl, ← hk]; ring⟩

theorem rel_antisymm (e : Fin n → ℂ) (he : Function.Injective e) (a b : Fin n)
    (h1 : Rel e a b) (h2 : Rel e b a) : a = b := by
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := h2
  have h3 : e a + ((k + l : ℕ) : ℂ) = e a := by push_cast; rw [← add_assoc, hk, hl]
  rw [add_eq_left] at h3
  have h4 : k + l = 0 := by exact_mod_cast h3
  have hk0 : k = 0 := by omega
  subst hk0
  apply he
  simpa using hk

def Mf (e : Fin n → ℂ) (Mc : P → Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ) (p : P) :
    Matrix (Idx n J R) (Idx n J R) ℂ :=
  Matrix.of fun s t => if s.2.2 = t.2.2 then
    ∑ a : Fin (d₂ + 1), (if e t.2.1 + ((a : ℕ) : ℂ) = e s.2.1 then Mc p a s.1 t.1 else 0) else 0

theorem Mf_apply (e : Fin n → ℂ) (Mc : P → Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ) (p : P)
    (s t : Idx n J R) : Mf e Mc p s t = if s.2.2 = t.2.2 then
      ∑ a : Fin (d₂ + 1), (if e t.2.1 + ((a : ℕ) : ℂ) = e s.2.1 then Mc p a s.1 t.1 else 0)
        else 0 := rfl

def projB (b : Fin n × Fin J) : (Idx n J R → ℂ) →L[ℂ] (Fin R → ℂ) :=
  ContinuousLinearMap.pi fun u => ContinuousLinearMap.proj (u, b)

theorem projB_apply (b : Fin n × Fin J) (G : Idx n J R → ℂ) (u : Fin R) :
    projB b G u = G (u, b) := rfl

def embB (b : Fin n × Fin J) : (Fin R → ℂ) →L[ℂ] (Idx n J R → ℂ) :=
  ContinuousLinearMap.pi fun s => (if s.2 = b then (1 : ℂ) else 0) • ContinuousLinearMap.proj s.1

theorem embB_apply (b : Fin n × Fin J) (v : Fin R → ℂ) (s : Idx n J R) :
    embB b v s = if s.2 = b then v s.1 else 0 := by
  unfold embB
  rw [ContinuousLinearMap.pi_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, boole_mul]

def innerA (e : Fin n → ℂ) (A : P → Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (p : P) (k : Fin d) (b : Fin n × Fin J) : (Idx n J R → ℂ) →L[ℂ] (Fin R → ℂ) :=
  ∑ a : Fin (d₂ + 1), ∑ i' : Fin n,
    if e i' + ((a : ℕ) : ℂ) = e b.1 then (A p k a).comp (projB (i', b.2)) else 0

theorem innerA_apply (e : Fin n → ℂ)
    (A : P → Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (p : P) (k : Fin d) (b : Fin n × Fin J) (G : Idx n J R → ℂ) (u : Fin R) :
    innerA e A p k b G u = ∑ a : Fin (d₂ + 1), ∑ i' : Fin n,
      if e i' + ((a : ℕ) : ℂ) = e b.1 then (A p k a (projB (i', b.2) G)) u else 0 := by
  simp only [innerA, ContinuousLinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i' _ => ?_
  split_ifs <;> rfl

def Af (e : Fin n → ℂ) (A : P → Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (p : P) (k : Fin d) : (Idx n J R → ℂ) →L[ℂ] (Idx n J R → ℂ) :=
  ∑ b : Fin n × Fin J, (embB b).comp (innerA (J := J) e A p k b)

theorem Af_apply (e : Fin n → ℂ)
    (A : P → Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (p : P) (k : Fin d) (G : Idx n J R → ℂ) (s : Idx n J R) :
    Af e A p k G s = innerA e A p k s.2 G s.1 := by
  simp only [Af, ContinuousLinearMap.sum_apply, Finset.sum_apply, ContinuousLinearMap.comp_apply,
    embB_apply]
  rw [Finset.sum_ite_eq]
  simp

def Ff (c : P → Fin n → Fin J → ℝ → (Fin R → ℂ)) (p : P) (z : ℝ) : Idx n J R → ℂ :=
  fun s => c p s.2.1 s.2.2 z s.1

theorem Ff_apply (c : P → Fin n → Fin J → ℝ → (Fin R → ℂ)) (p : P) (z : ℝ) (s : Idx n J R) :
    Ff c p z s = c p s.2.1 s.2.2 z s.1 := rfl

theorem projB_Ff (c : P → Fin n → Fin J → ℝ → (Fin R → ℂ)) (p : P) (z : ℝ) (i' : Fin n)
    (j : Fin J) : projB (i', j) (Ff c p z) = c p i' j z := rfl

theorem Mf_continuous [TopologicalSpace P] (e : Fin n → ℂ)
    (Mc : P → Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ) (hMc : ∀ a, Continuous fun p => Mc p a) :
    Continuous (Mf (J := J) e Mc) := by
  refine continuous_matrix fun s t => ?_
  simp only [Mf_apply]
  split_ifs
  · refine continuous_finsetSum _ fun a _ => ?_
    split_ifs
    · exact (hMc a).matrix_elem _ _
    · exact continuous_const
  · exact continuous_const

theorem Mf_bound (e : Fin n → ℂ) (Mc : P → Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ) (L : ℝ)
    (hMcL : ∀ p a i j, ‖Mc p a i j‖ ≤ L) (p : P) (s t : Idx n J R) :
    ‖Mf e Mc p s t‖ ≤ ((d₂ : ℝ) + 1) * ((n : ℝ) + 1) * |L| := by
  have h1 : ‖Mf e Mc p s t‖ ≤ ((d₂ : ℝ) + 1) * |L| := by
    rw [Mf_apply]
    split_ifs
    · calc ‖∑ a : Fin (d₂ + 1), (if e t.2.1 + ((a : ℕ) : ℂ) = e s.2.1 then Mc p a s.1 t.1 else 0)‖
            ≤ ∑ a : Fin (d₂ + 1),
                ‖(if e t.2.1 + ((a : ℕ) : ℂ) = e s.2.1 then Mc p a s.1 t.1 else 0)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _a : Fin (d₂ + 1), |L| := Finset.sum_le_sum fun a _ => by
            split_ifs
            · exact (hMcL p a _ _).trans (le_abs_self L)
            · simp
        _ = ((d₂ : ℝ) + 1) * |L| := by simp
    · simp only [norm_zero]
      positivity
  have h0 : 0 ≤ ((d₂ : ℝ) + 1) * |L| := by positivity
  have h2 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    linarith
  calc ‖Mf e Mc p s t‖ ≤ ((d₂ : ℝ) + 1) * |L| := h1
    _ ≤ ((n : ℝ) + 1) * (((d₂ : ℝ) + 1) * |L|) := le_mul_of_one_le_left h0 h2
    _ = ((d₂ : ℝ) + 1) * ((n : ℝ) + 1) * |L| := by ring

theorem projB_norm_le (b : Fin n × Fin J) (G : Idx n J R → ℂ) : ‖projB b G‖ ≤ ‖G‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg G)).2 fun u => by
    rw [projB_apply]; exact norm_le_pi_norm G _

theorem Af_continuous [TopologicalSpace P] (e : Fin n → ℂ)
    (A : P → Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (hA : ∀ k a, Continuous fun p => A p k a) (k : Fin d) :
    Continuous fun p => Af (J := J) e A p k := by
  unfold Af innerA
  refine continuous_finsetSum _ fun b _ => continuous_const.clm_comp ?_
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun i' _ => ?_
  split_ifs
  · exact (hA k a).clm_comp continuous_const
  · exact continuous_const

theorem Af_bound (e : Fin n → ℂ)
    (A : P → Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ))) (L : ℝ)
    (hAL : ∀ p k a, ‖A p k a‖ ≤ L) (p : P) (k : Fin d) :
    ‖Af (J := J) e A p k‖ ≤ ((d₂ : ℝ) + 1) * ((n : ℝ) + 1) * |L| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun G => ?_
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro s
  rw [Af_apply, innerA_apply]
  calc ‖∑ a : Fin (d₂ + 1), ∑ i' : Fin n,
          (if e i' + ((a : ℕ) : ℂ) = e s.2.1 then (A p k a (projB (i', s.2.2) G)) s.1 else 0)‖
        ≤ ∑ a : Fin (d₂ + 1), ‖∑ i' : Fin n,
          (if e i' + ((a : ℕ) : ℂ) = e s.2.1 then (A p k a (projB (i', s.2.2) G)) s.1 else 0)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ a : Fin (d₂ + 1), ∑ i' : Fin n,
          ‖(if e i' + ((a : ℕ) : ℂ) = e s.2.1 then (A p k a (projB (i', s.2.2) G)) s.1 else 0)‖ :=
        Finset.sum_le_sum fun a _ => norm_sum_le _ _
    _ ≤ ∑ _a : Fin (d₂ + 1), ∑ _i' : Fin n, |L| * ‖G‖ :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i' _ => by
          split_ifs
          · calc ‖(A p k a (projB (i', s.2.2) G)) s.1‖ ≤ ‖A p k a (projB (i', s.2.2) G)‖ :=
                  norm_le_pi_norm _ _
              _ ≤ ‖A p k a‖ * ‖projB (i', s.2.2) G‖ := ContinuousLinearMap.le_opNorm _ _
              _ ≤ |L| * ‖G‖ := mul_le_mul ((hAL p k a).trans (le_abs_self _))
                  (projB_norm_le _ _) (norm_nonneg _) (abs_nonneg _)
          · simp only [norm_zero]
            positivity
    _ = ((d₂ : ℝ) + 1) * (n : ℝ) * (|L| * ‖G‖) := by simp; ring
    _ ≤ ((d₂ : ℝ) + 1) * ((n : ℝ) + 1) * |L| * ‖G‖ := by
        have h0 : 0 ≤ ((d₂ : ℝ) + 1) * (|L| * ‖G‖) := by positivity
        nlinarith [h0]

theorem Ff_continuousOn [TopologicalSpace P] (c : P → Fin n → Fin J → ℝ → (Fin R → ℂ))
    (hcont : ∀ i j, ContinuousOn (fun w : P × ℝ => c w.1 i j w.2) (Set.univ ×ˢ Set.Ioc 0 1)) :
    ContinuousOn (fun w : P × ℝ => Ff c w.1 w.2) (Set.univ ×ˢ Set.Ioc 0 1) :=
  continuousOn_pi.2 fun s => (continuous_apply s.1).comp_continuousOn (hcont s.2.1 s.2.2)

theorem Ff_bound (c : P → Fin n → Fin J → ℝ → (Fin R → ℂ)) (m : ℝ) (B : P → ℝ)
    (hbound : ∀ p i j, ∀ z ∈ Set.Ioc (0 : ℝ) 1, ‖c p i j z‖ ≤ B p * z ^ (-m)) :
    ∀ p, ∀ z ∈ Set.Ioc (0 : ℝ) 1, ‖Ff c p z‖ ≤ max (B p) 0 * z ^ (-m) := by
  intro p z hz
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hz.1.le _))]
  intro s
  exact (norm_le_pi_norm (c p s.2.1 s.2.2 z) s.1).trans ((hbound p s.2.1 s.2.2 z hz).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hz.1.le _)))

theorem locbd_max [TopologicalSpace P] (B : P → ℝ)
    (hB : ∀ p₀ : P, ∃ B₀ : ℝ, ∀ᶠ p in nhds p₀, B p ≤ B₀) :
    ∀ p₀ : P, ∃ B₀ : ℝ, ∀ᶠ p in nhds p₀, max (B p) 0 ≤ B₀ := by
  intro p₀
  obtain ⟨B₀, h⟩ := hB p₀
  exact ⟨max B₀ 0, h.mono fun p hp => max_le_max hp le_rfl⟩

theorem sum_ite_const_zero {ι M : Type*} [AddCommMonoid M] (s : Finset ι) (Q : Prop) [Decidable Q]
    (f : ι → M) : (∑ x ∈ s, if Q then f x else 0) = if Q then ∑ x ∈ s, f x else 0 := by
  split_ifs <;> simp

theorem Ff_sys (e : Fin n → ℂ) (Mc : P → Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A : P → Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (c c' : P → Fin n → Fin J → ℝ → (Fin R → ℂ))
    (hsys : ∀ p i j, ∀ z ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt (c p i j) (c' p i j z) z ∧
      (z : ℂ) • c' p i j z = ∑ a : Fin (d₂ + 1), ∑ i' : Fin n, if e i' + (a : ℕ) = e i then
        Matrix.mulVec (Mc p a) (c p i' j z) + ∑ k : Fin d, ((z : ℂ) ^ ((k : ℕ) + 1)) • A p k a (c p i' j z)
      else 0) :
    ∀ p, ∀ z ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt (Ff c p) (Ff c' p z) z ∧
      (z : ℂ) • Ff c' p z =
        (fun s => ∑ t, Mf e Mc p s t • Ff c p z t) +
          ∑ k : Fin d, ((z : ℂ) ^ ((k : ℕ) + 1)) • Af e A p k (Ff c p z) := by
  intro p z hz
  refine ⟨hasDerivAt_pi.2 fun s => (hasDerivAt_pi.1 (hsys p s.2.1 s.2.2 z hz).1) s.1, ?_⟩
  funext s
  obtain ⟨u, i, j⟩ := s
  have h := congrFun (hsys p i j z hz).2 u
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, ite_apply, Pi.zero_apply,
    Pi.add_apply] at h
  simp only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul, Ff_apply, Af_apply,
    innerA_apply, projB_Ff]
  rw [h]

  have hT1 : (∑ t : Idx n J R, Mf e Mc p (u, (i, j)) t * c p t.2.1 t.2.2 z t.1) =
      ∑ a : Fin (d₂ + 1), ∑ i' : Fin n,
        if e i' + ((a : ℕ) : ℂ) = e i then (Matrix.mulVec (Mc p a) (c p i' j z)) u else 0 := by
    calc (∑ t : Idx n J R, Mf e Mc p (u, (i, j)) t * c p t.2.1 t.2.2 z t.1)
          = ∑ u' : Fin R, ∑ i' : Fin n, ∑ j' : Fin J,
              Mf e Mc p (u, (i, j)) (u', (i', j')) * c p i' j' z u' := by
          simp only [Fintype.sum_prod_type]
      _ = ∑ u' : Fin R, ∑ i' : Fin n,
            (∑ a : Fin (d₂ + 1), (if e i' + ((a : ℕ) : ℂ) = e i then Mc p a u u' else 0)) *
              c p i' j z u' := by
          refine Finset.sum_congr rfl fun u' _ => Finset.sum_congr rfl fun i' _ => ?_
          simp only [Mf_apply, ite_mul, zero_mul]
          rw [Finset.sum_ite_eq]
          simp
      _ = ∑ u' : Fin R, ∑ i' : Fin n, ∑ a : Fin (d₂ + 1),
            (if e i' + ((a : ℕ) : ℂ) = e i then Mc p a u u' * c p i' j z u' else 0) := by
          simp only [Finset.sum_mul, ite_mul, zero_mul]
      _ = ∑ a : Fin (d₂ + 1), ∑ i' : Fin n,
            if e i' + ((a : ℕ) : ℂ) = e i then (Matrix.mulVec (Mc p a) (c p i' j z)) u else 0 := by
          conv_lhs => rw [Finset.sum_comm]
          conv_rhs => rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i' _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [sum_ite_const_zero (M := ℂ)]
          rfl

  have hT2 : (∑ k : Fin d, (z : ℂ) ^ ((k : ℕ) + 1) *
      ∑ a : Fin (d₂ + 1), ∑ i' : Fin n,
        (if e i' + ((a : ℕ) : ℂ) = e i then (A p k a (c p i' j z)) u else 0)) =
      ∑ a : Fin (d₂ + 1), ∑ i' : Fin n,
        if e i' + ((a : ℕ) : ℂ) = e i then
          ∑ k : Fin d, (z : ℂ) ^ ((k : ℕ) + 1) * (A p k a (c p i' j z)) u else 0 := by
    simp only [Finset.mul_sum, mul_ite, mul_zero]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [sum_ite_const_zero (M := ℂ)]
  rw [hT1, hT2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i' _ => ?_
  split_ifs <;> simp

theorem Mf_aeval_pow (e : Fin n → ℂ) (he : Function.Injective e)
    (Mc : P → Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ) (q : ℂ[X])
    (hann : ∀ p, Polynomial.aeval (Mc p 0) q = 0) (p : P) :
    Polynomial.aeval (Mf (J := J) e Mc p) (q ^ n) = 0 := by
  have key := aeval_pow_card_eq_zero (σ := fun s : Idx n J R => s.2.1) (rel := Rel e)
    (rel_refl e) (rel_trans e) (rel_antisymm e he) (X := Mf e Mc p)
    (X' := blkAlgHom (Equiv.refl (Idx n J R)) (Mc p 0)) ⟨?_, ?_, ?_⟩ q
    (by rw [aeval_algHom_apply, hann p, map_zero])
  · simpa [Fintype.card_fin] using key
  ·
    intro s t h
    rw [Mf_apply]
    split_ifs
    · exact Finset.sum_eq_zero fun a _ => if_neg fun ha => h ⟨a, ha⟩
    · rfl
  ·
    intro s t h
    rw [blkAlgHom_apply, if_neg]
    intro hst
    apply h
    have : t.2.1 = s.2.1 := by
      show ((Equiv.refl (Idx n J R)).symm t).2.1 = ((Equiv.refl (Idx n J R)).symm s).2.1
      rw [hst]
    show Rel e t.2.1 s.2.1
    rw [this]
    exact rel_refl e _
  ·
    intro s t hst
    rw [Mf_apply, blkAlgHom_apply]
    have hcond : ∀ a : Fin (d₂ + 1), (e t.2.1 + ((a : ℕ) : ℂ) = e s.2.1) ↔ a = 0 := by
      intro a
      rw [show t.2.1 = s.2.1 from hst.symm, add_eq_left, Nat.cast_eq_zero]
      exact ⟨fun h => Fin.ext (by simpa using h), fun h => by simp [h]⟩
    simp_rw [hcond]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true, Equiv.refl_symm, Equiv.refl_apply]
    have h2 : (s.2 = t.2) ↔ (s.2.2 = t.2.2) := by
      rw [Prod.ext_iff]
      exact ⟨fun h => h.2, fun h => ⟨hst, h⟩⟩
    by_cases h3 : s.2.2 = t.2.2
    · rw [if_pos h3, if_pos (h2.2 h3)]
    · rw [if_neg h3, if_neg (fun h => h3 (h2.1 h))]

end Flatten

end RegSingFolded

open RegSingFolded in
theorem solution
    {n J R d₂ d : ℕ} (e : Fin n → ℂ) (he : Function.Injective e)
    (P : Type*) [TopologicalSpace P]
    (Mc : P → Fin (d₂ + 1) → Matrix (Fin R) (Fin R) ℂ)
    (A : P → Fin d → Fin (d₂ + 1) → ((Fin R → ℂ) →L[ℂ] (Fin R → ℂ)))
    (L : ℝ) (hMc : ∀ a, Continuous fun p => Mc p a) (hMcL : ∀ p a i j, ‖Mc p a i j‖ ≤ L)
    (hA : ∀ k a, Continuous fun p => A p k a) (hAL : ∀ p k a, ‖A p k a‖ ≤ L)
    (q : Polynomial ℂ) (hq : q ≠ 0) (hann : ∀ p, Polynomial.aeval (Mc p 0) q = 0)
    (c c' : P → Fin n → Fin J → ℝ → (Fin R → ℂ))
    (hcont : ∀ i j, ContinuousOn (fun w : P × ℝ => c w.1 i j w.2) (Set.univ ×ˢ Set.Ioc 0 1))
    (hsys : ∀ p i j, ∀ z ∈ Set.Ioc (0 : ℝ) 1, HasDerivAt (c p i j) (c' p i j z) z ∧
      (z : ℂ) • c' p i j z = ∑ a : Fin (d₂ + 1), ∑ i' : Fin n, if e i' + (a : ℕ) = e i then
        Matrix.mulVec (Mc p a) (c p i' j z) + ∑ k : Fin d, ((z : ℂ) ^ ((k : ℕ) + 1)) • A p k a (c p i' j z)
      else 0)
    (m : ℝ) (B : P → ℝ) (hB : ∀ p₀ : P, ∃ B₀ : ℝ, ∀ᶠ p in nhds p₀, B p ≤ B₀)
    (hbound : ∀ p i j, ∀ z ∈ Set.Ioc (0 : ℝ) 1, ‖c p i j z‖ ≤ B p * z ^ (-m))
    (ρ₂ θ : ℝ) (hθ : ∀ e' : ℂ, q.IsRoot e' → ∀ N : ℕ, ρ₂ < (e' + N).re → θ < (e' + N).re) :
    ∃ (D : ℕ) (S : Finset ℂ) (κ : ℝ), D ≤ n * q.natDegree ∧
      (∀ μ ∈ S, μ.re ≤ ρ₂ ∧ ∃ (e' : ℂ) (N : ℕ), q.IsRoot e' ∧ μ = e' + N) ∧
      ∃ c₂ : ℂ → ℕ → P → Fin n → Fin J → (Fin R → ℂ),
        (∀ μ j₂ i j, Continuous fun p => c₂ μ j₂ p i j) ∧
        ∀ p i j, (∀ μ j₂, ‖c₂ μ j₂ p i j‖ ≤ κ * B p) ∧
          ∀ z ∈ Set.Ioc (0 : ℝ) 1,
            ‖c p i j z - ∑ μ ∈ S, ∑ j₂ ∈ Finset.range D,
                ((z : ℂ) ^ μ * ((Real.log z : ℝ) : ℂ) ^ j₂) • c₂ μ j₂ p i j‖ ≤ κ * B p * z ^ θ := by
  have hroot : ∀ e' : ℂ, (q ^ n).IsRoot e' → q.IsRoot e' := by
    intro e' h
    rw [Polynomial.IsRoot, Polynomial.eval_pow] at h
    exact eq_zero_of_pow_eq_zero h
  have hθ' : ∀ e' : ℂ, (q ^ n).IsRoot e' → ∀ N : ℕ, ρ₂ < (e' + N).re → θ < (e' + N).re :=
    fun e' he' N hN => hθ e' (hroot e' he') N hN
  obtain ⟨D, S, κ, hD, hS, cc, hcc, hccp⟩ :=
    expansion_fintype (ι := Idx n J R) (P := P) (q ^ n) (pow_ne_zero n hq) d
      (((d₂ : ℝ) + 1) * ((n : ℝ) + 1) * |L|) m ρ₂ θ hθ' (Mf e Mc) (Af e A)
      (Mf_continuous e Mc hMc) (Mf_bound e Mc L hMcL) (Mf_aeval_pow e he Mc q hann)
      (Af_continuous e A hA) (Af_bound e A L hAL) (Ff c) (Ff c') (fun p => max (B p) 0)
      (Ff_continuousOn c hcont) (locbd_max B hB) (Ff_sys e Mc A c c' hsys) (Ff_bound c m B hbound)
  refine ⟨D, S, κ, hD.trans Polynomial.natDegree_pow_le, fun μ hμ => ?_,
    fun μ j₂ p i j u => cc μ j₂ p (u, (i, j)), fun μ j₂ i j => ?_, fun p i j => ?_⟩
  · obtain ⟨h1, e', N, he', hμ'⟩ := hS μ hμ
    exact ⟨h1, e', N, hroot e' he', hμ'⟩
  · exact continuous_pi fun u => (continuous_apply _).comp (hcc μ j₂)
  · have hBp : 0 ≤ B p := by
      have h1 := hbound p i j 1 ⟨one_pos, le_rfl⟩
      rw [Real.one_rpow, mul_one] at h1
      exact (norm_nonneg _).trans h1
    have hB'p : max (B p) 0 = B p := max_eq_left hBp
    obtain ⟨h1, h2⟩ := hccp p
    refine ⟨fun μ j₂ => ?_, fun z hz => ?_⟩
    · have hb := h1 μ j₂
      rw [hB'p] at hb
      have h0 : 0 ≤ κ * B p := (norm_nonneg _).trans hb
      exact (pi_norm_le_iff_of_nonneg h0).2 fun u =>
        (norm_le_pi_norm (cc μ j₂ p) (u, (i, j))).trans hb
    · have hr := h2 z hz
      rw [hB'p] at hr
      refine le_trans ?_ hr
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun u => ?_
      have : (c p i j z - ∑ μ ∈ S, ∑ j₂ ∈ Finset.range D,
            ((z : ℂ) ^ μ * ((Real.log z : ℝ) : ℂ) ^ j₂) • fun u => cc μ j₂ p (u, (i, j))) u =
          (Ff c p z - ∑ μ ∈ S, ∑ j₂ ∈ Finset.range D,
            ((z : ℂ) ^ μ * ((Real.log z : ℝ) : ℂ) ^ j₂) • cc μ j₂ p) (u, (i, j)) := by
        simp only [Ff_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
      rw [this]
      exact norm_le_pi_norm _ _

end
end S_RegularSingular_exists_expansion_coeff_of_folded_system
end P2MW
export P2MW.S_RegularSingular_exists_expansion_coeff_of_folded_system (solution)
