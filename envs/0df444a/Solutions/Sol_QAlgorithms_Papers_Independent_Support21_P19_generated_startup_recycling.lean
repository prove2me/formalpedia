-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P19.generated_startup_recycling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T17:35:55.622206+00:00
-- url     : https://prove2.me/submissions/fc28fdbc-1d45-4773-9a81-2ada9f7e8fd1

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P19
noncomputable section
open QAlgorithms QAlgorithms.Papers.Independent.Support21.P19
open scoped Matrix ComplexConjugate ComplexOrder
attribute [local instance] Classical.propDecidable Classical.decEq

@[simp] lemma g72gk2_split_join {a b : ℕ} (x : Fin a) (y : Fin b) : split (joinRegisters x y) = (x, y) :=
  finProdFinEquiv.symm_apply_apply (x, y)

lemma g72gk2_join_surj {a b : ℕ} (x : Fin (a*b)) : ∃ p q, x = joinRegisters (a := a) (b := b) p q :=
  ⟨(split x).1, (split x).2, (finProdFinEquiv.apply_symm_apply x).symm⟩

lemma g72gk2_sum_join {a b : ℕ} {M : Type*} [AddCommMonoid M] (f : Fin (a*b) → M) :
    ∑ k, f k = ∑ x : Fin a, ∑ y : Fin b, f (joinRegisters x y) := by
  rw [← Fintype.sum_prod_type', ← (finProdFinEquiv (m := a) (n := b)).sum_comp]; rfl

def g72gk2_kj {a b c d a' b' c' d' : ℕ} (A : Matrix (Fin a × Fin b) (Fin a' × Fin b') ℂ)
    (B : Matrix (Fin c × Fin d) (Fin c' × Fin d') ℂ) :
    Matrix (Fin (a*c) × Fin (b*d)) (Fin (a'*c') × Fin (b'*d')) ℂ :=
  fun i k => A ((split i.1).1, (split i.2).1) ((split k.1).1, (split k.2).1) *
    B ((split i.1).2, (split i.2).2) ((split k.1).2, (split k.2).2)

@[simp] lemma g72gk2_kj_jj {a b c d a' b' c' d' : ℕ} (A : Matrix (Fin a × Fin b) (Fin a' × Fin b') ℂ)
    (B : Matrix (Fin c × Fin d) (Fin c' × Fin d') ℂ) (x1 : Fin a) (x2 : Fin c) (y1 : Fin b) (y2 : Fin d)
    (z1 : Fin a') (z2 : Fin c') (w1 : Fin b') (w2 : Fin d') :
    g72gk2_kj A B (joinRegisters x1 x2, joinRegisters y1 y2) (joinRegisters z1 z2, joinRegisters w1 w2) =
      A (x1, y1) (z1, w1) * B (x2, y2) (z2, w2) := by
  simp [g72gk2_kj]

lemma g72gk2_star_ind (p : Prop) [Decidable p] : star (if p then (1:ℂ) else 0) = if p then 1 else 0 := by
  split_ifs <;> simp

lemma g72gk2_star_ite (p : Prop) [Decidable p] (x : ℂ) : star (if p then x else 0) = if p then star x else 0 := by
  split_ifs <;> simp

def g72gk2_jeq (a b c d : ℕ) : (Fin a × Fin b) × (Fin c × Fin d) ≃ Fin (a*c) × Fin (b*d) :=
  (Equiv.prodProdProdComm _ _ _ _).trans (finProdFinEquiv.prodCongr finProdFinEquiv)

lemma g72gk2_sum_j {a b c d : ℕ} (f : Fin (a*c) × Fin (b*d) → ℂ) :
    ∑ k, f k = ∑ x : Fin a × Fin b, ∑ u : Fin c × Fin d, f (joinRegisters x.1 u.1, joinRegisters x.2 u.2) := by
  rw [← Fintype.sum_prod_type', ← (g72gk2_jeq a b c d).sum_comp]; rfl

lemma g72gk2_extend_apply (R : Resource) (ma mb : ℕ) (M : Matrix (Fin (R.ai*ma) × Fin (R.bi*mb)) (Fin (R.ai*ma) × Fin (R.bi*mb)) ℂ) (i j : Fin (R.ao*ma) × Fin (R.bo*mb)) :
    extend R ma mb M i j = R.map (Matrix.of fun x y => M (joinRegisters x.1 (split i.1).2,joinRegisters x.2 (split i.2).2)
      (joinRegisters y.1 (split j.1).2,joinRegisters y.2 (split j.2).2))
    ((split i.1).1,(split i.2).1) ((split j.1).1,(split j.2).1) := rfl

lemma g72gk2_extend_conj (R : Resource) (A : Matrix (Fin R.ao × Fin R.bo) (Fin R.ai × Fin R.bi) ℂ)
    (hR : R.map = conjSuperop A) (ma mb : ℕ) :
    extend R ma mb = conjSuperop (g72gk2_kj A (1 : Matrix (Fin ma × Fin mb) (Fin ma × Fin mb) ℂ)) := by
  funext M i j
  rw [g72gk2_extend_apply]
  simp only [hR, conjSuperop, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [g72gk2_sum_j]
  simp only [g72gk2_sum_j (f := fun k => _ * star _), Finset.sum_mul]
  simp only [g72gk2_kj, g72gk2_split_join, Matrix.one_apply, Prod.mk.injEq, Fintype.sum_prod_type, ite_and,
    star_mul', g72gk2_star_ind, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_const_zero, Finset.sum_ite_irrel, g72gk2_star_ite, star_zero]

lemma g72gk2_tensor_conj (R S : Resource) (A : Matrix (Fin R.ao × Fin R.bo) (Fin R.ai × Fin R.bi) ℂ)
    (B : Matrix (Fin S.ao × Fin S.bo) (Fin S.ai × Fin S.bi) ℂ)
    (hR : R.map = conjSuperop A) (hS : S.map = conjSuperop B)
    (M : Matrix (Fin (R.ai*S.ai) × Fin (R.bi*S.bi)) (Fin (R.ai*S.ai) × Fin (R.bi*S.bi)) ℂ)
    (i j : Fin (R.ao*S.ao) × Fin (R.bo*S.bo)) :
    (tensorResources R S).map M i j = conjSuperop (g72gk2_kj A B) M i j := by
  simp only [tensorResources, hR, hS, conjSuperop, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [g72gk2_sum_j]
  simp only [g72gk2_sum_j (f := fun k => _ * star _), Finset.sum_mul]
  simp only [g72gk2_kj, g72gk2_split_join, Matrix.single_apply, Prod.mk.injEq, Fintype.sum_prod_type, ite_and,
    star_mul', g72gk2_star_ind, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_const_zero, Finset.sum_ite_irrel, g72gk2_star_ite, star_zero]
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun t => (t.2.2.1, t.2.2.2.1, t.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2, t.1, t.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1),
      invFun := fun r => (r.2.2.2.2.1, r.2.2.2.2.2.1, r.1, r.2.1, r.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2, r.2.2.1, r.2.2.2.1),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl } _ _ (fun x => ?_)
  simp only [Equiv.coe_fn_mk]; ring

lemma g72gk2_tensor_conj' (R S : Resource) (A : Matrix (Fin R.ao × Fin R.bo) (Fin R.ai × Fin R.bi) ℂ)
    (B : Matrix (Fin S.ao × Fin S.bo) (Fin S.ai × Fin S.bi) ℂ)
    (hR : R.map = conjSuperop A) (hS : S.map = conjSuperop B) :
    (tensorResources R S).map = conjSuperop (g72gk2_kj A B) :=
  funext fun M => funext fun i => funext fun j => g72gk2_tensor_conj R S A B hR hS M i j

def g72gk2_lk {a b c d : ℕ} (A : Matrix (Fin c) (Fin a) ℂ) (B : Matrix (Fin d) (Fin b) ℂ) :
    Matrix (Fin c × Fin d) (Fin a × Fin b) ℂ := fun i k => A i.1 k.1 * B i.2 k.2

lemma g72gk2_localMap_conj {a b c d : ℕ} (A : Matrix (Fin c) (Fin a) ℂ) (B : Matrix (Fin d) (Fin b) ℂ) :
    localMap (conjSuperop A) (conjSuperop B) = conjSuperop (g72gk2_lk A B) := by
  funext M i j
  show conjSuperop B (Matrix.of fun x y => conjSuperop A (Matrix.of fun u v => M (u,x) (v,y)) i.1 j.1) i.2 j.2 = _
  simp only [conjSuperop, g72gk2_lk, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum, star_mul']
  simp only [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv
    { toFun := fun x => (x.2.2.1, x.1, x.2.2.2, x.2.1), invFun := fun x => (x.2.1, x.2.2.2, x.1, x.2.2.1),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl } _ _ (fun x => ?_)
  simp only [Equiv.coe_fn_mk]; ring

lemma g72gk2_conj_comp {ι κ μ : Type*} [Fintype ι] [Fintype κ] (A : Matrix κ ι ℂ) (B : Matrix μ κ ℂ) :
    conjSuperop B ∘ conjSuperop A = conjSuperop (B * A) := by
  funext M; simp [conjSuperop, Matrix.mul_assoc, Matrix.conjTranspose_mul]

lemma g72gk2_isChannel_conj {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] (A : Matrix κ ι ℂ)
    (h : Aᴴ * A = 1) : IsChannel (conjSuperop A) :=
  ⟨1, fun _ => A, by simpa [IsKrausFamily] using h, fun ρ => by simp [krausApply, conjSuperop]⟩

/-- isometric sequential protocol with budget bound -/
def g72gk2_IS (L : Kind → Resource) (a b c d : ℕ) (n : Kind → ℕ)
    (X : Matrix (Fin c × Fin d) (Fin a × Fin b) ℂ) : Prop :=
  ∃ v : Kind → ℕ, (∀ k, v k ≤ n k) ∧ Sequential (D := Unit) L a b c d v (fun _ => conjSuperop X)

lemma g72gk2_IS_local (L : Kind → Resource) {a b c d : ℕ} (A : Matrix (Fin c) (Fin a) ℂ) (B : Matrix (Fin d) (Fin b) ℂ)
    (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) (n : Kind → ℕ) : g72gk2_IS L a b c d n (g72gk2_lk A B) := by
  refine ⟨fun _ => 0, fun _ => Nat.zero_le _, ?_⟩
  rw [← g72gk2_localMap_conj]
  exact Sequential.localStep (fun _ => conjSuperop A) _ (fun _ => g72gk2_isChannel_conj A hA) (g72gk2_isChannel_conj B hB)

lemma g72gk2_IS_call (L : Kind → Resource) (k : Kind) (W : Matrix (Fin (L k).ao × Fin (L k).bo) (Fin (L k).ai × Fin (L k).bi) ℂ)
    (hW : (L k).map = conjSuperop W) (ma mb : ℕ) (n : Kind → ℕ) (hn : 1 ≤ n k) :
    g72gk2_IS L ((L k).ai*ma) ((L k).bi*mb) ((L k).ao*ma) ((L k).bo*mb) n
      (g72gk2_kj W (1 : Matrix (Fin ma × Fin mb) (Fin ma × Fin mb) ℂ)) := by
  refine ⟨oneCall k, fun t => ?_, ?_⟩
  · unfold oneCall; split_ifs with h
    · subst h; exact hn
    · exact Nat.zero_le _
  · rw [← g72gk2_extend_conj (L k) W hW]
    exact Sequential.callStep k ma mb

lemma g72gk2_IS_comp {L : Kind → Resource} {a b c d e f : ℕ} {n n' : Kind → ℕ}
    {X : Matrix (Fin c × Fin d) (Fin a × Fin b) ℂ} {Y : Matrix (Fin e × Fin f) (Fin c × Fin d) ℂ}
    (hX : g72gk2_IS L a b c d n X) (hY : g72gk2_IS L c d e f n' Y) :
    g72gk2_IS L a b e f (fun k => n k + n' k) (Y * X) := by
  obtain ⟨v, hv, hsX⟩ := hX
  obtain ⟨w, hw, hsY⟩ := hY
  refine ⟨fun k => v k + w k, fun k => Nat.add_le_add (hv k) (hw k), ?_⟩
  have := Sequential.compose hsX hsY
  rwa [g72gk2_conj_comp] at this

lemma g72gk2_IS_mono {L : Kind → Resource} {a b c d : ℕ} {n n' : Kind → ℕ}
    {X : Matrix (Fin c × Fin d) (Fin a × Fin b) ℂ} (hX : g72gk2_IS L a b c d n X) (h : ∀ k, n k ≤ n' k) :
    g72gk2_IS L a b c d n' X := by
  obtain ⟨v, hv, hs⟩ := hX
  exact ⟨v, fun k => (hv k).trans (h k), hs⟩

lemma g72gk2_IS_exact {U T : Resource} {n : Kind → ℕ} {X : Matrix (Fin T.ao × Fin T.bo) (Fin T.ai × Fin T.bi) ℂ}
    (hT : T.map = conjSuperop X) (h : g72gk2_IS (library U) T.ai T.bi T.ao T.bo n X) : Exact U n T := by
  obtain ⟨v, hv, hs⟩ := h
  exact ⟨v, hv, by rw [hT]; exact hs⟩

/-- permutation matrix of an equivalence -/
def g72gk2_pm {α β : Type*} (e : α ≃ β) : Matrix β α ℂ := fun i k => if e k = i then 1 else 0

lemma g72gk2_pm_mul {α β γ : Type*} [Fintype α] (e : α ≃ β) (X : Matrix α γ ℂ) :
    g72gk2_pm e * X = fun i k => X (e.symm i) k := by
  funext i k
  simp only [g72gk2_pm, Matrix.mul_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (e.symm i)]
  · simp
  · intro b _ hb; rw [if_neg]; intro h; exact hb (by rw [← h]; simp)
  · simp

lemma g72gk2_mul_pm {α β γ : Type*} [Fintype β] (e : α ≃ β) (X : Matrix γ β ℂ) :
    X * g72gk2_pm e = fun i k => X i (e k) := by
  funext i k
  simp only [g72gk2_pm, Matrix.mul_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (e k)] <;> simp (config := {contextual := true}) [eq_comm]

lemma g72gk2_pm_iso {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] (e : α ≃ β) :
    (g72gk2_pm e)ᴴ * g72gk2_pm e = 1 := by
  rw [g72gk2_mul_pm]; funext i k
  simp [g72gk2_pm, Matrix.one_apply, eq_comm]


@[simp] lemma g72gk2_join_inj {a b : ℕ} (x x' : Fin a) (y y' : Fin b) :
    joinRegisters x y = joinRegisters x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h; have := congrArg split h; simpa using this
  · rintro ⟨rfl, rfl⟩; rfl

/-- signed functional matrix -/
def g72gk2_sf {α β : Type*} (f : α → β) (g : α → ℂ) : Matrix β α ℂ := fun i k => if f k = i then g k else 0

lemma g72gk2_mul_sf {α β γ : Type*} [Fintype β] (f : α → β) (g : α → ℂ) (X : Matrix γ β ℂ) :
    X * g72gk2_sf f g = fun i k => X i (f k) * g k := by
  funext i k
  simp only [g72gk2_sf, Matrix.mul_apply, mul_ite, mul_zero]
  rw [Finset.sum_eq_single (f k)] <;> simp (config := {contextual := true}) [eq_comm]

lemma g72gk2_sf_iso {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] (f : α → β) (g : α → ℂ)
    (hf : Function.Injective f) (hg : ∀ k, star (g k) * g k = 1) :
    (g72gk2_sf f g)ᴴ * g72gk2_sf f g = 1 := by
  rw [g72gk2_mul_sf]; funext i k
  simp only [Matrix.conjTranspose_apply, g72gk2_sf, Matrix.one_apply]
  by_cases h : i = k
  · subst h; simpa [hg] using hg i
  · rw [if_neg (fun h' => h (hf h')), if_neg h]; simp

def g72gk2_one1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ := fun _ _ => 1

lemma g72gk2_idle_pt (M : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) (i j : Fin 1 × Fin 1) :
    (idle 1 1).map M i j = conjSuperop g72gk2_one1 M i j := by
  rw [Subsingleton.elim i (0, 0), Subsingleton.elim j (0, 0)]
  simp [idle, conjSuperop, g72gk2_one1, Matrix.mul_apply, Fintype.sum_prod_type]

lemma g72gk2_idle_map : (idle 1 1).map = conjSuperop g72gk2_one1 :=
  funext fun M => funext fun i => funext fun j => g72gk2_idle_pt M i j

def g72gk2_s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
lemma g72gk2_ss : g72gk2_s * g72gk2_s = 1/2 := by
  unfold g72gk2_s
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
lemma g72gk2_star_s : star g72gk2_s = g72gk2_s := by
  unfold g72gk2_s; simp [Complex.conj_ofReal]

lemma g72gk2_conj_s : (starRingEnd ℂ) g72gk2_s = g72gk2_s := g72gk2_star_s

def g72gk2_Ve : Matrix (Fin 2 × Fin 2) (Fin 1 × Fin 1) ℂ := fun p _ => if p.1 = p.2 then g72gk2_s else 0

lemma g72gk2_ent_pt (M : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) (i j : Fin 2 × Fin 2) :
    (entangled 2).map M i j = conjSuperop g72gk2_Ve M i j := by
  simp [entangled, pureDensity, maximallyEntangledKet, finiteMaxEntangled, conjSuperop, g72gk2_Ve,
    Matrix.mul_apply, g72gk2_s, Fintype.sum_prod_type]
  split_ifs <;> simp <;> ring

lemma g72gk2_ent_map : (entangled 2).map = conjSuperop g72gk2_Ve :=
  funext fun M => funext fun i => funext fun j => g72gk2_ent_pt M i j

def g72gk2_Vc : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 1) ℂ := fun i k => if i.1 = k.1 ∧ i.2 = k.1 then 1 else 0

lemma g72gk2_cob_pt (M : Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℂ) (i j : Fin 2 × Fin 2) :
    (cobitChannel 2).map M i j = conjSuperop g72gk2_Vc M i j := by
  fin_cases i <;> fin_cases j <;>
    simp [cobitChannel, conjSuperop, g72gk2_Vc, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

lemma g72gk2_cob_map : (cobitChannel 2).map = conjSuperop g72gk2_Vc :=
  funext fun M => funext fun i => funext fun j => g72gk2_cob_pt M i j

def g72gk2_Vq : Matrix (Fin 1 × Fin 2) (Fin 2 × Fin 1) ℂ := fun i k => if i.2 = k.1 then 1 else 0

lemma g72gk2_qub_pt (M : Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℂ) (i j : Fin 1 × Fin 2) :
    (qubitChannel 2).map M i j = conjSuperop g72gk2_Vq M i j := by
  fin_cases i <;> fin_cases j <;>
    simp [qubitChannel, conjSuperop, g72gk2_Vq, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

lemma g72gk2_qub_map : (qubitChannel 2).map = conjSuperop g72gk2_Vq :=
  funext fun M => funext fun i => funext fun j => g72gk2_qub_pt M i j

def g72gk2_cm (R : Resource) (V : Matrix (Fin R.ao × Fin R.bo) (Fin R.ai × Fin R.bi) ℂ) :
    (m : ℕ) → Matrix (Fin (resourceTensorCopies R m).ao × Fin (resourceTensorCopies R m).bo)
      (Fin (resourceTensorCopies R m).ai × Fin (resourceTensorCopies R m).bi) ℂ
  | 0 => g72gk2_one1
  | m+1 => g72gk2_kj V (g72gk2_cm R V m)

lemma g72gk2_cm_map (R : Resource) (V : Matrix (Fin R.ao × Fin R.bo) (Fin R.ai × Fin R.bi) ℂ)
    (hV : R.map = conjSuperop V) : ∀ m, (resourceTensorCopies R m).map = conjSuperop (g72gk2_cm R V m)
  | 0 => g72gk2_idle_map
  | m+1 => g72gk2_tensor_conj' R _ V _ hV (g72gk2_cm_map R V hV m)

def g72gk2_Hd : Matrix (Fin 2) (Fin 2) ℂ := fun i k => if i = 1 ∧ k = 1 then -g72gk2_s else g72gk2_s
def g72gk2_sg (a z : Fin 2) : ℂ := if a = 1 ∧ z = 1 then -1 else 1

lemma g72gk2_lk_sf {a b c d : ℕ} (f : Fin a → Fin c) (g : Fin a → ℂ) (f' : Fin b → Fin d) (g' : Fin b → ℂ) :
    g72gk2_lk (g72gk2_sf f g) (g72gk2_sf f' g') = g72gk2_sf (Prod.map f f') (fun k => g k.1 * g' k.2) := by
  funext i k
  simp only [g72gk2_lk, g72gk2_sf, Prod.map, Prod.ext_iff]
  split_ifs <;> simp_all


lemma g72gk2_sfb_mul {α β γ : Type*} [Fintype α] (f : α → β) (g : α → ℂ) (h : β → α)
    (hfh : ∀ j, h (f j) = j) (hhf : ∀ i, f (h i) = i) (X : Matrix α γ ℂ) :
    g72gk2_sf f g * X = fun i k => g (h i) * X (h i) k := by
  funext i k
  simp only [g72gk2_sf, Matrix.mul_apply, ite_mul, zero_mul]
  rw [Finset.sum_eq_single (h i)]
  · rw [if_pos (hhf i)]
  · intro j _ hj; rw [if_neg]; intro e; exact hj (by rw [← e, hfh])
  · simp

lemma g72gk2_cob_mul {P Y : ℕ} {γ : Type*} (X : Matrix (Fin (2*P) × Fin (1*Y)) γ ℂ) (i1 : Fin (2*P)) (i2 : Fin (2*Y)) (k : γ) :
    (g72gk2_kj g72gk2_Vc (1 : Matrix (Fin P × Fin Y) (Fin P × Fin Y) ℂ) * X) (i1, i2) k =
      if (split i2).1 = (split i1).1 then X (i1, joinRegisters 0 (split i2).2) k else 0 := by
  obtain ⟨a, r, rfl⟩ := g72gk2_join_surj i1
  obtain ⟨c, y, rfl⟩ := g72gk2_join_surj i2
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, g72gk2_sum_join, g72gk2_kj_jj, g72gk2_Vc, Matrix.one_apply,
    g72gk2_split_join, Prod.mk.injEq, ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_const_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Fin.sum_univ_one, Fin.isValue]
  try (by_cases h : c = a <;> simp_all)

lemma g72gk2_f2 (x y : Fin 2) : x + y + y = x := by fin_cases x <;> fin_cases y <;> rfl

section P1
variable {Qa Qb Qo QB Ea Eb Eo EB ma mb : ℕ}

def g72gk2_fA0 : Fin (((2*Qa)*(1*(1*Ea)))*ma) → Fin ((Qa*(1*Ea))*(2*ma)) := fun k =>
  joinRegisters (joinRegisters (split (split (split k).1).1).2 (split (split (split k).1).2).2)
    (joinRegisters (split (split (split k).1).1).1 (split k).2)

def g72gk2_fB0 : Fin (((1*Qb)*(1*(1*Eb)))*mb) → Fin ((Qb*(1*Eb))*mb) := fun k =>
  joinRegisters (joinRegisters (split (split (split k).1).1).2 (split (split (split k).1).2).2) (split k).2

/-- Bell rotation on (q0, eA): output (a, b, (qo, eo), an) -/
def g72gk2_A2 : Matrix (Fin (2*(2*((Qo*Eo)*ma)))) (Fin ((Qo*(2*Eo))*(2*ma))) ℂ := fun i k =>
  if (split (split i).2).1 = (split (split k).2).1 + (split (split (split k).1).2).1 ∧
     (split (split i).2).2 = joinRegisters (joinRegisters (split (split k).1).1 (split (split (split k).1).2).2)
        (split (split k).2).2
  then g72gk2_Hd (split i).1 (split (split k).2).1 else 0

def g72gk2_fB2 : Fin ((QB*(2*EB))*mb) → Fin (1*((QB*(2*EB))*mb)) := fun k => joinRegisters 0 k

def g72gk2_fA4 : Fin (2*(2*((Qo*Eo)*ma))) → Fin (2*(2*((Qo*Eo)*ma))) := fun k =>
  joinRegisters (split (split k).2).1 (joinRegisters (split k).1 (split (split k).2).2)

def g72gk2_fB4 : Fin (2*((QB*(2*EB))*mb)) → Fin (1*(2*((QB*(2*EB))*mb))) := fun k => joinRegisters 0 k

def g72gk2_fA6 : Fin (2*(2*((Qo*Eo)*ma))) → Fin (((1*Qo)*(2*(2*Eo)))*ma) := fun k =>
  joinRegisters (joinRegisters (joinRegisters 0 (split (split (split (split k).2).2).1).1)
    (joinRegisters (split (split k).2).1 (joinRegisters (split k).1 (split (split (split (split k).2).2).1).2)))
    (split (split (split k).2).2).2

def g72gk2_fB6 : Fin (2*(2*((QB*(2*EB))*mb))) → Fin (((2*QB)*(2*(2*EB)))*mb) := fun k =>
  joinRegisters (joinRegisters (joinRegisters
      ((split (split (split (split (split k).2).2).1).2).1 + (split k).1)
      (split (split (split (split k).2).2).1).1)
    (joinRegisters (split (split k).2).1 (joinRegisters (split k).1
      (split (split (split (split (split k).2).2).1).2).2)))
    (split (split (split k).2).2).2

def g72gk2_gB6 : Fin (2*(2*((QB*(2*EB))*mb))) → ℂ := fun k =>
  g72gk2_sg (split (split k).2).1 ((split (split (split (split (split k).2).2).1).2).1 + (split k).1)

variable (Q : Matrix (Fin Qo × Fin QB) (Fin Qa × Fin Qb) ℂ) (E : Matrix (Fin Eo × Fin EB) (Fin Ea × Fin Eb) ℂ)

def g72gk2_S0 : Matrix (Fin ((Qa*(1*Ea))*(2*ma)) × Fin ((Qb*(1*Eb))*mb)) (Fin (((2*Qa)*(1*(1*Ea)))*ma) × Fin (((1*Qb)*(1*(1*Eb)))*mb)) ℂ :=
  g72gk2_lk (g72gk2_sf g72gk2_fA0 (fun _ => 1)) (g72gk2_sf g72gk2_fB0 (fun _ => 1))
def g72gk2_IHm : Matrix (Fin ((Qo*(2*Eo))*(2*ma)) × Fin ((QB*(2*EB))*mb)) (Fin ((Qa*(1*Ea))*(2*ma)) × Fin ((Qb*(1*Eb))*mb)) ℂ :=
  g72gk2_kj (g72gk2_kj Q (g72gk2_kj g72gk2_Ve E)) (1 : Matrix (Fin (2*ma) × Fin mb) (Fin (2*ma) × Fin mb) ℂ)
def g72gk2_S2 : Matrix (Fin (2*(2*((Qo*Eo)*ma))) × Fin (1*((QB*(2*EB))*mb))) (Fin ((Qo*(2*Eo))*(2*ma)) × Fin ((QB*(2*EB))*mb)) ℂ :=
  g72gk2_lk g72gk2_A2 (g72gk2_sf g72gk2_fB2 (fun _ => 1))
def g72gk2_C3 : Matrix (Fin (2*(2*((Qo*Eo)*ma))) × Fin (2*((QB*(2*EB))*mb))) (Fin (2*(2*((Qo*Eo)*ma))) × Fin (1*((QB*(2*EB))*mb))) ℂ :=
  g72gk2_kj g72gk2_Vc (1 : Matrix (Fin (2*((Qo*Eo)*ma)) × Fin ((QB*(2*EB))*mb)) (Fin (2*((Qo*Eo)*ma)) × Fin ((QB*(2*EB))*mb)) ℂ)
def g72gk2_S4 : Matrix (Fin (2*(2*((Qo*Eo)*ma))) × Fin (1*(2*((QB*(2*EB))*mb)))) (Fin (2*(2*((Qo*Eo)*ma))) × Fin (2*((QB*(2*EB))*mb))) ℂ :=
  g72gk2_lk (g72gk2_sf g72gk2_fA4 (fun _ => 1)) (g72gk2_sf g72gk2_fB4 (fun _ => 1))
def g72gk2_C5 : Matrix (Fin (2*(2*((Qo*Eo)*ma))) × Fin (2*(2*((QB*(2*EB))*mb)))) (Fin (2*(2*((Qo*Eo)*ma))) × Fin (1*(2*((QB*(2*EB))*mb)))) ℂ :=
  g72gk2_kj g72gk2_Vc (1 : Matrix (Fin (2*((Qo*Eo)*ma)) × Fin (2*((QB*(2*EB))*mb))) (Fin (2*((Qo*Eo)*ma)) × Fin (2*((QB*(2*EB))*mb))) ℂ)
def g72gk2_S6 : Matrix (Fin (((1*Qo)*(2*(2*Eo)))*ma) × Fin (((2*QB)*(2*(2*EB)))*mb)) (Fin (2*(2*((Qo*Eo)*ma))) × Fin (2*(2*((QB*(2*EB))*mb)))) ℂ :=
  g72gk2_lk (g72gk2_sf g72gk2_fA6 (fun _ => 1)) (g72gk2_sf g72gk2_fB6 g72gk2_gB6)
def g72gk2_T1 : Matrix (Fin (((1*Qo)*(2*(2*Eo)))*ma) × Fin (((2*QB)*(2*(2*EB)))*mb)) (Fin (((2*Qa)*(1*(1*Ea)))*ma) × Fin (((1*Qb)*(1*(1*Eb)))*mb)) ℂ :=
  g72gk2_kj (g72gk2_kj (g72gk2_kj g72gk2_Vq Q) (g72gk2_kj g72gk2_Ve (g72gk2_kj g72gk2_Ve E)))
      (1 : Matrix (Fin ma × Fin mb) (Fin ma × Fin mb) ℂ)


def g72gk2_h6A : Fin (((1*Qo)*(2*(2*Eo)))*ma) → Fin (2*(2*((Qo*Eo)*ma))) := fun i =>
  joinRegisters (split (split (split (split i).1).2).2).1 (joinRegisters (split (split (split i).1).2).1
    (joinRegisters (joinRegisters (split (split (split i).1).1).2 (split (split (split (split i).1).2).2).2) (split i).2))

def g72gk2_h6B : Fin (((2*QB)*(2*(2*EB)))*mb) → Fin (2*(2*((QB*(2*EB))*mb))) := fun i =>
  joinRegisters (split (split (split (split i).1).2).2).1 (joinRegisters (split (split (split i).1).2).1
    (joinRegisters (joinRegisters (split (split (split i).1).1).2
      (joinRegisters ((split (split (split i).1).1).1 + (split (split (split (split i).1).2).2).1)
        (split (split (split (split i).1).2).2).2)) (split i).2))

lemma g72gk2_S6_app {γ : Type*} (X : Matrix (Fin (2*(2*((Qo*Eo)*ma))) × Fin (2*(2*((QB*(2*EB))*mb)))) γ ℂ) i k :
    (g72gk2_S6 (Qo := Qo) (Eo := Eo) (ma := ma) (QB := QB) (EB := EB) (mb := mb) * X) i k = g72gk2_gB6 (g72gk2_h6B i.2) * X (g72gk2_h6A i.1, g72gk2_h6B i.2) k := by
  unfold g72gk2_S6
  rw [g72gk2_lk_sf, g72gk2_sfb_mul _ _ (Prod.map g72gk2_h6A g72gk2_h6B)]
  · simp only [one_mul]; rfl
  · rintro ⟨j1, j2⟩
    obtain ⟨b, j1, rfl⟩ := g72gk2_join_surj j1
    obtain ⟨a, j1, rfl⟩ := g72gk2_join_surj j1
    obtain ⟨j1, an, rfl⟩ := g72gk2_join_surj j1
    obtain ⟨qo, eo, rfl⟩ := g72gk2_join_surj j1
    obtain ⟨bB, j2, rfl⟩ := g72gk2_join_surj j2
    obtain ⟨aB, j2, rfl⟩ := g72gk2_join_surj j2
    obtain ⟨j2, bn, rfl⟩ := g72gk2_join_surj j2
    obtain ⟨qB, j2, rfl⟩ := g72gk2_join_surj j2
    obtain ⟨eB, ebr, rfl⟩ := g72gk2_join_surj j2
    simp [g72gk2_h6A, g72gk2_h6B, g72gk2_fA6, g72gk2_fB6, g72gk2_f2]
  · rintro ⟨i1, i2⟩
    obtain ⟨i1, an, rfl⟩ := g72gk2_join_surj i1
    obtain ⟨i1, i1', rfl⟩ := g72gk2_join_surj i1
    obtain ⟨u, qo, rfl⟩ := g72gk2_join_surj i1
    obtain ⟨a, i1', rfl⟩ := g72gk2_join_surj i1'
    obtain ⟨b, eo, rfl⟩ := g72gk2_join_surj i1'
    obtain ⟨i2, bn, rfl⟩ := g72gk2_join_surj i2
    obtain ⟨i2, i2', rfl⟩ := g72gk2_join_surj i2
    obtain ⟨z, qB, rfl⟩ := g72gk2_join_surj i2
    obtain ⟨a', i2', rfl⟩ := g72gk2_join_surj i2'
    obtain ⟨b', eB, rfl⟩ := g72gk2_join_surj i2'
    simp [g72gk2_h6A, g72gk2_h6B, g72gk2_fA6, g72gk2_fB6, g72gk2_f2, Fin.fin_one_eq_zero u]

lemma g72gk2_S4_app {γ : Type*} (X : Matrix (Fin (2*(2*((Qo*Eo)*ma))) × Fin (2*((QB*(2*EB))*mb))) γ ℂ) i k :
    (g72gk2_S4 (Qo := Qo) (Eo := Eo) (ma := ma) (QB := QB) (EB := EB) (mb := mb) * X) i k = X (g72gk2_fA4 i.1, (split i.2).2) k := by
  unfold g72gk2_S4
  rw [g72gk2_lk_sf, g72gk2_sfb_mul _ _ (Prod.map g72gk2_fA4 (fun i => (split i).2))]
  · simp only [one_mul]; rfl
  · rintro ⟨j1, j2⟩
    obtain ⟨b, j1, rfl⟩ := g72gk2_join_surj j1
    obtain ⟨a, r, rfl⟩ := g72gk2_join_surj j1
    simp [g72gk2_fA4, g72gk2_fB4]
  · rintro ⟨j1, j2⟩
    obtain ⟨b, j1, rfl⟩ := g72gk2_join_surj j1
    obtain ⟨a, r, rfl⟩ := g72gk2_join_surj j1
    obtain ⟨u, y, rfl⟩ := g72gk2_join_surj j2
    simp [g72gk2_fA4, g72gk2_fB4, Fin.fin_one_eq_zero u]

lemma g72gk2_S2_app {γ : Type*} (X : Matrix (Fin ((Qo*(2*Eo))*(2*ma)) × Fin ((QB*(2*EB))*mb)) γ ℂ) i k :
    (g72gk2_S2 (Qo := Qo) (Eo := Eo) (ma := ma) (QB := QB) (EB := EB) (mb := mb) * X) i k = ∑ j, g72gk2_A2 i.1 j * X (j, (split i.2).2) k := by
  obtain ⟨i1, i2⟩ := i
  obtain ⟨u, y, rfl⟩ := g72gk2_join_surj i2
  simp only [g72gk2_S2, Matrix.mul_apply, Fintype.sum_prod_type, g72gk2_lk, g72gk2_sf, g72gk2_fB2, g72gk2_join_inj,
    g72gk2_split_join, Fin.fin_one_eq_zero u, true_and, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma g72gk2_Z_app j k :
    (g72gk2_IHm (ma := ma) (mb := mb) Q E * g72gk2_S0 (Qa := Qa) (Ea := Ea) (ma := ma) (Qb := Qb) (Eb := Eb) (mb := mb)) j k =
      g72gk2_IHm Q E j (g72gk2_fA0 k.1, g72gk2_fB0 k.2) := by
  unfold g72gk2_S0; rw [g72gk2_lk_sf, g72gk2_mul_sf]; simp only [mul_one]; rfl

set_option maxHeartbeats 4000000 in
lemma g72gk2_p1_mat :
    g72gk2_T1 (ma := ma) (mb := mb) Q E = g72gk2_S6 (Qo := Qo) (Eo := Eo) (ma := ma) (QB := QB) (EB := EB) (mb := mb) * (g72gk2_C5 (Qo := Qo) (Eo := Eo) (ma := ma) (QB := QB) (EB := EB) (mb := mb) * (g72gk2_S4 (Qo := Qo) (Eo := Eo) (ma := ma) (QB := QB) (EB := EB) (mb := mb) *
      (g72gk2_C3 (Qo := Qo) (Eo := Eo) (ma := ma) (QB := QB) (EB := EB) (mb := mb) * (g72gk2_S2 (Qo := Qo) (Eo := Eo) (ma := ma) (QB := QB) (EB := EB) (mb := mb) * (g72gk2_IHm (ma := ma) (mb := mb) Q E *
        g72gk2_S0 (Qa := Qa) (Ea := Ea) (ma := ma) (Qb := Qb) (Eb := Eb) (mb := mb)))))) := by
  funext ⟨i1, i2⟩ ⟨k1, k2⟩
  rw [g72gk2_S6_app]
  obtain ⟨i1, an, rfl⟩ := g72gk2_join_surj i1
  obtain ⟨i1, i1', rfl⟩ := g72gk2_join_surj i1
  obtain ⟨u, qo, rfl⟩ := g72gk2_join_surj i1
  obtain ⟨a, i1', rfl⟩ := g72gk2_join_surj i1'
  obtain ⟨b, eo, rfl⟩ := g72gk2_join_surj i1'
  obtain ⟨i2, bn, rfl⟩ := g72gk2_join_surj i2
  obtain ⟨i2, i2', rfl⟩ := g72gk2_join_surj i2
  obtain ⟨z, qB, rfl⟩ := g72gk2_join_surj i2
  obtain ⟨a', i2', rfl⟩ := g72gk2_join_surj i2'
  obtain ⟨b', eB, rfl⟩ := g72gk2_join_surj i2'
  simp only [g72gk2_h6A, g72gk2_h6B, g72gk2_split_join]
  unfold g72gk2_C5; rw [g72gk2_cob_mul]
  simp only [g72gk2_split_join, g72gk2_S4_app, g72gk2_fA4]
  unfold g72gk2_C3; rw [g72gk2_cob_mul]
  simp only [g72gk2_split_join, g72gk2_S2_app, g72gk2_Z_app]
  obtain ⟨k1, an', rfl⟩ := g72gk2_join_surj k1
  obtain ⟨k1, k1', rfl⟩ := g72gk2_join_surj k1
  obtain ⟨x, qa, rfl⟩ := g72gk2_join_surj k1
  obtain ⟨w, k1', rfl⟩ := g72gk2_join_surj k1'
  obtain ⟨w', ea, rfl⟩ := g72gk2_join_surj k1'
  obtain ⟨k2, bn', rfl⟩ := g72gk2_join_surj k2
  obtain ⟨k2, k2', rfl⟩ := g72gk2_join_surj k2
  obtain ⟨v, qb, rfl⟩ := g72gk2_join_surj k2
  obtain ⟨v1, k2', rfl⟩ := g72gk2_join_surj k2'
  obtain ⟨v2, eb, rfl⟩ := g72gk2_join_surj k2'
  simp only [g72gk2_fA0, g72gk2_fB0, g72gk2_split_join, g72gk2_IHm, g72gk2_T1, g72gk2_kj_jj, g72gk2_sum_join,
    g72gk2_A2, g72gk2_Ve, g72gk2_Vq, Matrix.one_apply, Prod.mk.injEq, g72gk2_join_inj]
  simp only [ite_and, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, g72gk2_gB6,
    g72gk2_split_join, g72gk2_f2]
  by_cases ha : a' = a
  · subst ha
    by_cases hb : b' = b
    · subst hb
      fin_cases a' <;> fin_cases b' <;> fin_cases z <;> fin_cases x <;> simp [g72gk2_Hd, g72gk2_sg] <;> split_ifs <;> ring
    · simp [hb, Ne.symm hb]
  · simp [ha, Ne.symm ha]
end P1

section P1b
variable {Qa Qb Qo QB Ea Eb Eo EB ma mb : ℕ}

lemma g72gk2_inj_of_left {α β : Type*} {f : α → β} (h : β → α) (hh : ∀ j, h (f j) = j) : Function.Injective f :=
  fun a b e => by rw [← hh a, ← hh b, e]

def g72gk2_hA0 : Fin ((Qa*(1*Ea))*(2*ma)) → Fin (((2*Qa)*(1*(1*Ea)))*ma) := fun k =>
  joinRegisters (joinRegisters (joinRegisters (split (split k).2).1 (split (split k).1).1)
    (joinRegisters 0 (split (split k).1).2)) (split (split k).2).2

def g72gk2_hB0 : Fin ((Qb*(1*Eb))*mb) → Fin (((1*Qb)*(1*(1*Eb)))*mb) := fun k =>
  joinRegisters (joinRegisters (joinRegisters 0 (split (split k).1).1)
    (joinRegisters 0 (split (split k).1).2)) (split k).2

lemma g72gk2_fA0_inj : Function.Injective (g72gk2_fA0 (Qa := Qa) (Ea := Ea) (ma := ma)) := by
  refine g72gk2_inj_of_left g72gk2_hA0 (fun k => ?_)
  obtain ⟨k1, an', rfl⟩ := g72gk2_join_surj k
  obtain ⟨k1, k1', rfl⟩ := g72gk2_join_surj k1
  obtain ⟨x, qa, rfl⟩ := g72gk2_join_surj k1
  obtain ⟨w, k1', rfl⟩ := g72gk2_join_surj k1'
  simp [g72gk2_fA0, g72gk2_hA0, Fin.fin_one_eq_zero w]

lemma g72gk2_fB0_inj : Function.Injective (g72gk2_fB0 (Qb := Qb) (Eb := Eb) (mb := mb)) := by
  refine g72gk2_inj_of_left g72gk2_hB0 (fun k => ?_)
  obtain ⟨k1, an', rfl⟩ := g72gk2_join_surj k
  obtain ⟨k1, k1', rfl⟩ := g72gk2_join_surj k1
  obtain ⟨x, qa, rfl⟩ := g72gk2_join_surj k1
  obtain ⟨w, k1', rfl⟩ := g72gk2_join_surj k1'
  simp [g72gk2_fB0, g72gk2_hB0, Fin.fin_one_eq_zero w, Fin.fin_one_eq_zero x]

lemma g72gk2_J0_inj {Y : ℕ} : Function.Injective (fun k : Fin Y => joinRegisters (0 : Fin 1) k) :=
  g72gk2_inj_of_left (fun i => (split i).2) (fun k => by simp)

lemma g72gk2_fA4_inj : Function.Injective (g72gk2_fA4 (Qo := Qo) (Eo := Eo) (ma := ma)) := by
  refine g72gk2_inj_of_left g72gk2_fA4 (fun k => ?_)
  obtain ⟨b, j1, rfl⟩ := g72gk2_join_surj k
  obtain ⟨a, r, rfl⟩ := g72gk2_join_surj j1
  simp [g72gk2_fA4]

lemma g72gk2_fA6_inj : Function.Injective (g72gk2_fA6 (Qo := Qo) (Eo := Eo) (ma := ma)) := by
  refine g72gk2_inj_of_left g72gk2_h6A (fun j1 => ?_)
  obtain ⟨b, j1, rfl⟩ := g72gk2_join_surj j1
  obtain ⟨a, j1, rfl⟩ := g72gk2_join_surj j1
  obtain ⟨j1, an, rfl⟩ := g72gk2_join_surj j1
  obtain ⟨qo, eo, rfl⟩ := g72gk2_join_surj j1
  simp [g72gk2_h6A, g72gk2_fA6]

lemma g72gk2_fB6_inj : Function.Injective (g72gk2_fB6 (QB := QB) (EB := EB) (mb := mb)) := by
  refine g72gk2_inj_of_left g72gk2_h6B (fun j2 => ?_)
  obtain ⟨bB, j2, rfl⟩ := g72gk2_join_surj j2
  obtain ⟨aB, j2, rfl⟩ := g72gk2_join_surj j2
  obtain ⟨j2, bn, rfl⟩ := g72gk2_join_surj j2
  obtain ⟨qB, j2, rfl⟩ := g72gk2_join_surj j2
  obtain ⟨eB, ebr, rfl⟩ := g72gk2_join_surj j2
  simp [g72gk2_h6B, g72gk2_fB6, g72gk2_f2]

lemma g72gk2_sg_abs (a z : Fin 2) : star (g72gk2_sg a z) * g72gk2_sg a z = 1 := by
  unfold g72gk2_sg; split_ifs <;> simp

lemma g72gk2_A2_iso : (g72gk2_A2 (Qo := Qo) (Eo := Eo) (ma := ma))ᴴ * g72gk2_A2 (Qo := Qo) (Eo := Eo) (ma := ma) = 1 := by
  funext k k'
  obtain ⟨k1, k2, rfl⟩ := g72gk2_join_surj k
  obtain ⟨qo, k1, rfl⟩ := g72gk2_join_surj k1
  obtain ⟨eA, eo, rfl⟩ := g72gk2_join_surj k1
  obtain ⟨x, an, rfl⟩ := g72gk2_join_surj k2
  obtain ⟨k1, k2, rfl⟩ := g72gk2_join_surj k'
  obtain ⟨qo', k1, rfl⟩ := g72gk2_join_surj k1
  obtain ⟨eA', eo', rfl⟩ := g72gk2_join_surj k1
  obtain ⟨x', an', rfl⟩ := g72gk2_join_surj k2
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, g72gk2_A2, g72gk2_sum_join, g72gk2_split_join,
    g72gk2_join_inj, Matrix.one_apply]
  simp only [ite_and, g72gk2_star_ite, star_zero, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
  by_cases h1 : qo = qo'
  · subst h1
    by_cases h2 : eo = eo'
    · subst h2
      by_cases h3 : an = an'
      · subst h3
        fin_cases x <;> fin_cases x' <;> fin_cases eA <;> fin_cases eA' <;>
          simp [g72gk2_Hd, Fin.sum_univ_two, g72gk2_star_s, g72gk2_conj_s, g72gk2_ss] <;> norm_num
      · simp [h3, Ne.symm h3]
    · simp [h2, Ne.symm h2]
  · simp [h1, Ne.symm h1]

end P1b

section P1c
variable {Qa Qb Qo QB Ea Eb Eo EB : ℕ}

lemma g72gk2_sf1_iso {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] {f : α → β} (hf : Function.Injective f) :
    (g72gk2_sf f (fun _ => 1))ᴴ * g72gk2_sf f (fun _ => 1) = 1 :=
  g72gk2_sf_iso f _ hf (fun _ => by simp)

lemma g72gk2_p1_step (Q : Matrix (Fin Qo × Fin QB) (Fin Qa × Fin Qb) ℂ) (E : Matrix (Fin Eo × Fin EB) (Fin Ea × Fin Eb) ℂ)
    (n : Kind → ℕ)
    (hIH : ∀ ma mb, g72gk2_IS (library (cobitChannel 2)) ((Qa*(1*Ea))*ma) ((Qb*(1*Eb))*mb) ((Qo*(2*Eo))*ma) ((QB*(2*EB))*mb) n
      (g72gk2_kj (g72gk2_kj Q (g72gk2_kj g72gk2_Ve E)) (1 : Matrix (Fin ma × Fin mb) (Fin ma × Fin mb) ℂ)))
    (ma mb : ℕ) :
    g72gk2_IS (library (cobitChannel 2)) (((2*Qa)*(1*(1*Ea)))*ma) (((1*Qb)*(1*(1*Eb)))*mb)
      (((1*Qo)*(2*(2*Eo)))*ma) (((2*QB)*(2*(2*EB)))*mb) (fun k => n k + budget 2 0 0 0 0 0 0 0 k)
      (g72gk2_kj (g72gk2_kj (g72gk2_kj g72gk2_Vq Q) (g72gk2_kj g72gk2_Ve (g72gk2_kj g72gk2_Ve E)))
        (1 : Matrix (Fin ma × Fin mb) (Fin ma × Fin mb) ℂ)) := by
  have e := g72gk2_p1_mat (ma := ma) (mb := mb) Q E
  unfold g72gk2_T1 at e
  rw [e]
  have h0 : g72gk2_IS (library (cobitChannel 2)) _ _ _ _ (fun _ => 0)
      (g72gk2_S0 (Qa := Qa) (Ea := Ea) (ma := ma) (Qb := Qb) (Eb := Eb) (mb := mb)) :=
    g72gk2_IS_local _ _ _ (g72gk2_sf1_iso g72gk2_fA0_inj) (g72gk2_sf1_iso g72gk2_fB0_inj) _
  have h1 : g72gk2_IS (library (cobitChannel 2)) _ _ _ _ n (g72gk2_IHm (ma := ma) (mb := mb) Q E) := hIH (2*ma) mb
  have h2 : g72gk2_IS (library (cobitChannel 2)) _ _ _ _ (fun _ => 0)
      (g72gk2_S2 (Qo := Qo) (Eo := Eo) (ma := ma) (QB := QB) (EB := EB) (mb := mb)) :=
    g72gk2_IS_local _ _ _ g72gk2_A2_iso (g72gk2_sf1_iso g72gk2_J0_inj) _
  have h3 : g72gk2_IS (library (cobitChannel 2)) (2*(2*((Qo*Eo)*ma))) (1*((QB*(2*EB))*mb)) (2*(2*((Qo*Eo)*ma)))
      (2*((QB*(2*EB))*mb)) (budget 1 0 0 0 0 0 0 0)
      (g72gk2_C3 (Qo := Qo) (Eo := Eo) (ma := ma) (QB := QB) (EB := EB) (mb := mb)) :=
    g72gk2_IS_call (library (cobitChannel 2)) Kind.main g72gk2_Vc g72gk2_cob_map _ _ _ (by decide)
  have h4 : g72gk2_IS (library (cobitChannel 2)) _ _ _ _ (fun _ => 0)
      (g72gk2_S4 (Qo := Qo) (Eo := Eo) (ma := ma) (QB := QB) (EB := EB) (mb := mb)) :=
    g72gk2_IS_local _ _ _ (g72gk2_sf1_iso g72gk2_fA4_inj) (g72gk2_sf1_iso g72gk2_J0_inj) _
  have h5 : g72gk2_IS (library (cobitChannel 2)) (2*(2*((Qo*Eo)*ma))) (1*(2*((QB*(2*EB))*mb))) (2*(2*((Qo*Eo)*ma)))
      (2*(2*((QB*(2*EB))*mb))) (budget 1 0 0 0 0 0 0 0)
      (g72gk2_C5 (Qo := Qo) (Eo := Eo) (ma := ma) (QB := QB) (EB := EB) (mb := mb)) :=
    g72gk2_IS_call (library (cobitChannel 2)) Kind.main g72gk2_Vc g72gk2_cob_map _ _ _ (by decide)
  have h6 : g72gk2_IS (library (cobitChannel 2)) _ _ _ _ (fun _ => 0)
      (g72gk2_S6 (Qo := Qo) (Eo := Eo) (ma := ma) (QB := QB) (EB := EB) (mb := mb)) :=
    g72gk2_IS_local _ _ _ (g72gk2_sf1_iso g72gk2_fA6_inj)
      (g72gk2_sf_iso _ _ g72gk2_fB6_inj (fun k => g72gk2_sg_abs _ _)) _
  refine g72gk2_IS_mono (g72gk2_IS_comp (g72gk2_IS_comp (g72gk2_IS_comp (g72gk2_IS_comp (g72gk2_IS_comp
    (g72gk2_IS_comp h0 h1) h2) h3) h4) h5) h6) ?_
  intro k; cases k <;> simp [budget]

end P1c

/-- remove trivial ancillas -/
lemma g72gk2_IS_unanc {L : Kind → Resource} {a b c d : ℕ} {n : Kind → ℕ}
    (X : Matrix (Fin c × Fin d) (Fin a × Fin b) ℂ)
    (h : g72gk2_IS L (a*1) (b*1) (c*1) (d*1) n (g72gk2_kj X (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ))) :
    g72gk2_IS L a b c d n X := by
  have hin : g72gk2_IS L a b (a*1) (b*1) (fun _ => 0)
      (g72gk2_lk (g72gk2_sf (fun k : Fin a => joinRegisters k (0 : Fin 1)) (fun _ => 1))
        (g72gk2_sf (fun k : Fin b => joinRegisters k (0 : Fin 1)) (fun _ => 1))) :=
    g72gk2_IS_local _ _ _ (g72gk2_sf1_iso (g72gk2_inj_of_left (fun i => (split i).1) (fun k => by simp)))
      (g72gk2_sf1_iso (g72gk2_inj_of_left (fun i => (split i).1) (fun k => by simp))) _
  have hout : g72gk2_IS L (c*1) (d*1) c d (fun _ => 0)
      (g72gk2_lk (g72gk2_sf (fun k : Fin (c*1) => (split k).1) (fun _ => 1))
        (g72gk2_sf (fun k : Fin (d*1) => (split k).1) (fun _ => 1))) :=
    g72gk2_IS_local _ _ _ (g72gk2_sf1_iso (g72gk2_inj_of_left (fun i => joinRegisters i (0 : Fin 1))
        (fun k => by obtain ⟨x, y, rfl⟩ := g72gk2_join_surj k; simp [Fin.fin_one_eq_zero y])))
      (g72gk2_sf1_iso (g72gk2_inj_of_left (fun i => joinRegisters i (0 : Fin 1))
        (fun k => by obtain ⟨x, y, rfl⟩ := g72gk2_join_surj k; simp [Fin.fin_one_eq_zero y]))) _
  have := g72gk2_IS_mono (g72gk2_IS_comp (g72gk2_IS_comp hin h) hout) (n' := n) (fun k => by simp)
  convert this using 1
  funext ⟨i1, i2⟩ ⟨k1, k2⟩
  simp only [Matrix.mul_apply, g72gk2_lk, Fintype.sum_prod_type, g72gk2_sum_join, g72gk2_sf, Prod.map, g72gk2_split_join,
    Prod.mk.injEq, g72gk2_kj_jj, Matrix.one_apply, mul_one, Fin.sum_univ_one, Fin.isValue]
  simp [g72gk2_join_inj, ite_and]

lemma g72gk2_fin111 (x y : Fin (1*(1*1))) : x = y := by
  apply Fin.ext; have := x.isLt; have := y.isLt; first | omega | (simp at *; omega) | simp at *

def g72gk2_Ap {m : ℕ} : Matrix (Fin (2*m)) (Fin ((1*(1*1))*m)) ℂ := fun i k => if (split i).2 = (split k).2 then g72gk2_s else 0
def g72gk2_fBp {m : ℕ} : Fin ((1*(1*1))*m) → Fin (1*m) := fun k => joinRegisters 0 (split k).2
def g72gk2_fF {m : ℕ} : Fin (2*m) → Fin ((1*(2*1))*m) := fun k =>
  joinRegisters (joinRegisters 0 (joinRegisters (split k).1 0)) (split k).2
def g72gk2_hF {m : ℕ} : Fin ((1*(2*1))*m) → Fin (2*m) := fun i =>
  joinRegisters (split (split (split i).1).2).1 (split i).2

lemma g72gk2_hF_fF {m : ℕ} (k : Fin (2*m)) : g72gk2_hF (g72gk2_fF k) = k := by
  obtain ⟨x, y, rfl⟩ := g72gk2_join_surj k; simp [g72gk2_hF, g72gk2_fF]
lemma g72gk2_fF_hF {m : ℕ} (i : Fin ((1*(2*1))*m)) : g72gk2_fF (g72gk2_hF i) = i := by
  obtain ⟨i, an, rfl⟩ := g72gk2_join_surj i
  obtain ⟨u, i, rfl⟩ := g72gk2_join_surj i
  obtain ⟨c, w, rfl⟩ := g72gk2_join_surj i
  simp [g72gk2_hF, g72gk2_fF, Fin.fin_one_eq_zero u, Fin.fin_one_eq_zero w]

lemma g72gk2_Ap_iso {m : ℕ} : (g72gk2_Ap (m := m))ᴴ * g72gk2_Ap (m := m) = 1 := by
  funext k k'
  obtain ⟨k1, an, rfl⟩ := g72gk2_join_surj k
  obtain ⟨k1', an', rfl⟩ := g72gk2_join_surj k'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, g72gk2_Ap, g72gk2_sum_join, g72gk2_split_join,
    Matrix.one_apply, g72gk2_join_inj]
  rw [g72gk2_fin111 k1 k1']
  by_cases h : an = an'
  · subst h; simp [Fin.sum_univ_two, g72gk2_conj_s, g72gk2_ss] <;> norm_num
  · simp [h, Ne.symm h]

lemma g72gk2_fBp_inj {m : ℕ} : Function.Injective (g72gk2_fBp (m := m)) := by
  intro k k' e
  obtain ⟨k1, an, rfl⟩ := g72gk2_join_surj k
  obtain ⟨k1', an', rfl⟩ := g72gk2_join_surj k'
  simp [g72gk2_fBp] at e
  rw [g72gk2_fin111 k1 k1', e]

lemma g72gk2_p1_base (ma mb : ℕ) :
    g72gk2_IS (library (cobitChannel 2)) ((1*(1*1))*ma) ((1*(1*1))*mb) ((1*(2*1))*ma) ((1*(2*1))*mb)
      (budget 1 0 0 0 0 0 0 0)
      (g72gk2_kj (g72gk2_kj g72gk2_one1 (g72gk2_kj g72gk2_Ve g72gk2_one1)) (1 : Matrix (Fin ma × Fin mb) (Fin ma × Fin mb) ℂ)) := by
  have hP : g72gk2_IS (library (cobitChannel 2)) ((1*(1*1))*ma) ((1*(1*1))*mb) (2*ma) (1*mb) (fun _ => 0)
      (g72gk2_lk g72gk2_Ap (g72gk2_sf g72gk2_fBp (fun _ => 1))) :=
    g72gk2_IS_local _ _ _ g72gk2_Ap_iso (g72gk2_sf1_iso g72gk2_fBp_inj) _
  have hC : g72gk2_IS (library (cobitChannel 2)) (2*ma) (1*mb) (2*ma) (2*mb) (budget 1 0 0 0 0 0 0 0)
      (g72gk2_kj g72gk2_Vc (1 : Matrix (Fin ma × Fin mb) (Fin ma × Fin mb) ℂ)) :=
    g72gk2_IS_call (library (cobitChannel 2)) Kind.main g72gk2_Vc g72gk2_cob_map _ _ _ (by decide)
  have hF : g72gk2_IS (library (cobitChannel 2)) (2*ma) (2*mb) ((1*(2*1))*ma) ((1*(2*1))*mb) (fun _ => 0)
      (g72gk2_lk (g72gk2_sf g72gk2_fF (fun _ => 1)) (g72gk2_sf g72gk2_fF (fun _ => 1))) :=
    g72gk2_IS_local _ _ _ (g72gk2_sf1_iso (g72gk2_inj_of_left _ g72gk2_hF_fF))
      (g72gk2_sf1_iso (g72gk2_inj_of_left _ g72gk2_hF_fF)) _
  have := g72gk2_IS_mono (g72gk2_IS_comp (g72gk2_IS_comp hP hC) hF) (n' := budget 1 0 0 0 0 0 0 0)
    (fun k => by cases k <;> simp [budget])
  convert this using 1
  rw [g72gk2_lk_sf, g72gk2_sfb_mul _ _ (Prod.map g72gk2_hF g72gk2_hF) (fun j => by simp [Prod.map, g72gk2_hF_fF])
    (fun i => by simp [Prod.map, g72gk2_fF_hF])]
  funext ⟨i1, i2⟩ ⟨k1, k2⟩
  simp only [Prod.map, one_mul]
  rw [g72gk2_cob_mul]
  obtain ⟨i1, an, rfl⟩ := g72gk2_join_surj i1
  obtain ⟨u, i1, rfl⟩ := g72gk2_join_surj i1
  obtain ⟨c, w, rfl⟩ := g72gk2_join_surj i1
  obtain ⟨i2, bn, rfl⟩ := g72gk2_join_surj i2
  obtain ⟨u', i2, rfl⟩ := g72gk2_join_surj i2
  obtain ⟨c', w', rfl⟩ := g72gk2_join_surj i2
  obtain ⟨k1, an', rfl⟩ := g72gk2_join_surj k1
  obtain ⟨k2, bn', rfl⟩ := g72gk2_join_surj k2
  obtain ⟨v1, k1, rfl⟩ := g72gk2_join_surj k1
  obtain ⟨v2, v3, rfl⟩ := g72gk2_join_surj k1
  obtain ⟨t1, k2, rfl⟩ := g72gk2_join_surj k2
  obtain ⟨t2, t3, rfl⟩ := g72gk2_join_surj k2
  simp only [g72gk2_hF, g72gk2_split_join, Matrix.mul_apply, Fintype.sum_prod_type, g72gk2_sum_join, g72gk2_lk,
    g72gk2_sf, g72gk2_fBp, g72gk2_Ap, g72gk2_join_inj, g72gk2_kj_jj, g72gk2_one1, g72gk2_Ve, Matrix.one_apply,
    Prod.mk.injEq]
  simp only [ite_and, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, Fin.sum_univ_one]
  split_ifs <;> simp_all

abbrev g72gk2_T (m : ℕ) : Resource :=
  tensorResources (resourceTensorCopies (qubitChannel 2) m) (resourceTensorCopies (entangled 2) (m+1))

lemma g72gk2_p1_all : ∀ m ma mb, g72gk2_IS (library (cobitChannel 2)) ((g72gk2_T m).ai*ma) ((g72gk2_T m).bi*mb)
    ((g72gk2_T m).ao*ma) ((g72gk2_T m).bo*mb) (budget (2*m+1) 0 0 0 0 0 0 0)
    (g72gk2_kj (g72gk2_kj (g72gk2_cm (qubitChannel 2) g72gk2_Vq m) (g72gk2_cm (entangled 2) g72gk2_Ve (m+1)))
      (1 : Matrix (Fin ma × Fin mb) (Fin ma × Fin mb) ℂ))
  | 0, ma, mb => g72gk2_p1_base ma mb
  | m+1, ma, mb => by
    have := g72gk2_p1_step (g72gk2_cm (qubitChannel 2) g72gk2_Vq m) (g72gk2_cm (entangled 2) g72gk2_Ve m)
      (budget (2*m+1) 0 0 0 0 0 0 0) (fun ma mb => g72gk2_p1_all m ma mb) ma mb
    refine g72gk2_IS_mono this ?_
    intro k; cases k <;> simp [budget]; omega

lemma g72gk2_part1 (m : ℕ) : Exact (cobitChannel 2) (budget (2*m+1) 0 0 0 0 0 0 0) (g72gk2_T m) :=
  g72gk2_IS_exact (g72gk2_tensor_conj' _ _ _ _ (g72gk2_cm_map _ _ g72gk2_qub_map m) (g72gk2_cm_map _ _ g72gk2_ent_map (m+1)))
    (g72gk2_IS_unanc _ (g72gk2_p1_all m 1 1))

lemma g72gk2_exact_mono {U T : Resource} {b b' : Kind → ℕ} (h : Exact U b T) (hb : ∀ k, b k ≤ b' k) : Exact U b' T := by
  obtain ⟨v, hv, hs⟩ := h; exact ⟨v, fun k => (hv k).trans (hb k), hs⟩

lemma g72gk2_part3 : ∀ delta > 0, ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n ≥ n0, ∃ m eo : ℕ,
      (n : ℝ)*(1/2-delta) ≤ m ∧ (n : ℝ)*(1/2-delta) ≤ eo ∧
      Exact (cobitChannel 2) (budget n 0 0 0 0 0 0 0)
        (tensorResources (resourceTensorCopies (qubitChannel 2) m) (resourceTensorCopies (entangled 2) eo)) := by
  intro delta hd
  refine ⟨⌈1/delta⌉₊ + 1, by omega, fun n hn => ⟨(n-1)/2, (n-1)/2+1, ?_, ?_, ?_⟩⟩
  · have h1 : (n : ℝ) ≤ 2*(((n-1)/2 : ℕ) : ℝ) + 2 := by
      have : n ≤ 2*((n-1)/2) + 2 := by omega
      exact_mod_cast this
    have h2 : 1/delta < n := by
      have := Nat.le_ceil (1/delta)
      have h3 : ((⌈1/delta⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h3; linarith
    have h4 : 1 < n*delta := by rw [div_lt_iff₀ hd] at h2; linarith
    nlinarith
  · have h1 : (n : ℝ) ≤ 2*(((n-1)/2 : ℕ) : ℝ) + 2 := by
      have : n ≤ 2*((n-1)/2) + 2 := by omega
      exact_mod_cast this
    have h2 : 1/delta < n := by
      have := Nat.le_ceil (1/delta)
      have h3 : ((⌈1/delta⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h3; linarith
    have h4 : 1 < n*delta := by rw [div_lt_iff₀ hd] at h2; linarith
    push_cast; nlinarith
  · refine g72gk2_exact_mono (g72gk2_part1 ((n-1)/2)) ?_
    have : 1 ≤ n := le_trans (by omega) hn
    intro k; cases k <;> simp [budget]; omega

lemma g72gk2_s2 : g72gk2_s ^ 2 = 1/2 := by rw [sq, g72gk2_ss]

lemma g72gk2_ent_mul {P Y : ℕ} {γ : Type*} (X : Matrix (Fin (1*P) × Fin (1*Y)) γ ℂ) (i1 : Fin (2*P)) (i2 : Fin (2*Y)) (k : γ) :
    (g72gk2_kj g72gk2_Ve (1 : Matrix (Fin P × Fin Y) (Fin P × Fin Y) ℂ) * X) (i1, i2) k =
      (if (split i1).1 = (split i2).1 then g72gk2_s else 0) * X (joinRegisters 0 (split i1).2, joinRegisters 0 (split i2).2) k := by
  obtain ⟨a, r, rfl⟩ := g72gk2_join_surj i1
  obtain ⟨c, y, rfl⟩ := g72gk2_join_surj i2
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, g72gk2_sum_join, g72gk2_kj_jj, g72gk2_Ve, Matrix.one_apply,
    g72gk2_split_join, Prod.mk.injEq, ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_const_zero, Finset.sum_ite_irrel, Fin.sum_univ_one, Fin.isValue]
  split_ifs <;> simp_all

lemma g72gk2_qub_mul {P Y : ℕ} {γ : Type*} (X : Matrix (Fin (2*P) × Fin (1*Y)) γ ℂ) (i1 : Fin (1*P)) (i2 : Fin (2*Y)) (k : γ) :
    (g72gk2_kj g72gk2_Vq (1 : Matrix (Fin P × Fin Y) (Fin P × Fin Y) ℂ) * X) (i1, i2) k =
      X (joinRegisters (split i2).1 (split i1).2, joinRegisters 0 (split i2).2) k := by
  obtain ⟨a, r, rfl⟩ := g72gk2_join_surj i1
  obtain ⟨c, y, rfl⟩ := g72gk2_join_surj i2
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, g72gk2_sum_join, g72gk2_kj_jj, g72gk2_Vq, Matrix.one_apply,
    g72gk2_split_join, Prod.mk.injEq, ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.sum_const_zero, Finset.sum_ite_irrel, Fin.sum_univ_one, Fin.isValue]

/-- Bob's Bell decoder: (y, e) -> (o1, o2) -/
def g72gk2_D : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := fun o i =>
  if o.1 = i.1 + i.2 then g72gk2_s * g72gk2_sg o.2 i.1 * g72gk2_sg o.1 o.2 else 0

section P2
variable {Ca Cb Co CB ma mb : ℕ}

def g72gk2_gA0 : Fin ((2*(2*Ca))*ma) → Fin (Ca*(2*(2*ma))) := fun k =>
  joinRegisters (split (split (split k).1).2).2
    (joinRegisters (split (split k).1).1 (joinRegisters (split (split (split k).1).2).1 (split k).2))
def g72gk2_iA0 : Fin (Ca*(2*(2*ma))) → Fin ((2*(2*Ca))*ma) := fun k =>
  joinRegisters (joinRegisters (split (split k).2).1 (joinRegisters (split (split (split k).2).2).1 (split k).1))
    (split (split (split k).2).2).2
def g72gk2_gB0 : Fin ((1*(1*Cb))*mb) → Fin (Cb*mb) := fun k =>
  joinRegisters (split (split (split k).1).2).2 (split k).2
def g72gk2_iB0 : Fin (Cb*mb) → Fin ((1*(1*Cb))*mb) := fun k =>
  joinRegisters (joinRegisters 0 (joinRegisters 0 (split k).1)) (split k).2

def g72gk2_gA2 : Fin (Co*(2*(2*ma))) → Fin (1*(2*(2*(Co*ma)))) := fun k =>
  joinRegisters 0 (joinRegisters (split (split k).2).1 (joinRegisters (split (split (split k).2).2).1
    (joinRegisters (split k).1 (split (split (split k).2).2).2)))
def g72gk2_iA2 : Fin (1*(2*(2*(Co*ma)))) → Fin (Co*(2*(2*ma))) := fun i =>
  joinRegisters (split (split (split (split i).2).2).2).1 (joinRegisters (split (split i).2).1
    (joinRegisters (split (split (split i).2).2).1 (split (split (split (split i).2).2).2).2))

/-- Alice's controlled X^x1 Z^x2 on her EPR half -/
def g72gk2_gA4 : Fin (2*(2*(2*(Co*ma)))) → Fin (2*(2*(2*(Co*ma)))) := fun k =>
  joinRegisters ((split k).1 + (split (split k).2).1) (split k).2
def g72gk2_sA4 : Fin (2*(2*(2*(Co*ma)))) → ℂ := fun k => g72gk2_sg (split (split (split k).2).2).1 (split k).1

def g72gk2_gA6 : Fin (1*(2*(2*(Co*ma)))) → Fin ((2*(2*Co))*ma) := fun k =>
  joinRegisters (joinRegisters (split (split k).2).1 (joinRegisters (split (split (split k).2).2).1
    (split (split (split (split k).2).2).2).1)) (split (split (split (split k).2).2).2).2
def g72gk2_iA6 : Fin ((2*(2*Co))*ma) → Fin (1*(2*(2*(Co*ma)))) := fun i =>
  joinRegisters 0 (joinRegisters (split (split i).1).1 (joinRegisters (split (split (split i).1).2).1
    (joinRegisters (split (split (split i).1).2).2 (split i).2)))

def g72gk2_B6 : Matrix (Fin ((2*(2*CB))*mb)) (Fin (2*(2*(CB*mb)))) ℂ := fun i k =>
  if (split (split k).2).2 = joinRegisters (split (split (split i).1).2).2 (split i).2 then
    g72gk2_D ((split (split i).1).1, (split (split (split i).1).2).1) ((split k).1, (split (split k).2).1) else 0

def g72gk2_R0 : Matrix (Fin (Ca*(2*(2*ma))) × Fin (Cb*mb)) (Fin ((2*(2*Ca))*ma) × Fin ((1*(1*Cb))*mb)) ℂ :=
  g72gk2_lk (g72gk2_sf g72gk2_gA0 (fun _ => 1)) (g72gk2_sf g72gk2_gB0 (fun _ => 1))
def g72gk2_R2 : Matrix (Fin (1*(2*(2*(Co*ma)))) × Fin (1*(CB*mb))) (Fin (Co*(2*(2*ma))) × Fin (CB*mb)) ℂ :=
  g72gk2_lk (g72gk2_sf g72gk2_gA2 (fun _ => 1)) (g72gk2_sf (fun k : Fin (CB*mb) => joinRegisters (0 : Fin 1) k) (fun _ => 1))
def g72gk2_R3 : Matrix (Fin (2*(2*(2*(Co*ma)))) × Fin (2*(CB*mb))) (Fin (1*(2*(2*(Co*ma)))) × Fin (1*(CB*mb))) ℂ :=
  g72gk2_kj g72gk2_Ve (1 : Matrix (Fin (2*(2*(Co*ma))) × Fin (CB*mb)) (Fin (2*(2*(Co*ma))) × Fin (CB*mb)) ℂ)
def g72gk2_R4 : Matrix (Fin (2*(2*(2*(Co*ma)))) × Fin (1*(2*(CB*mb)))) (Fin (2*(2*(2*(Co*ma)))) × Fin (2*(CB*mb))) ℂ :=
  g72gk2_lk (g72gk2_sf g72gk2_gA4 g72gk2_sA4) (g72gk2_sf (fun k : Fin (2*(CB*mb)) => joinRegisters (0 : Fin 1) k) (fun _ => 1))
def g72gk2_R5 : Matrix (Fin (1*(2*(2*(Co*ma)))) × Fin (2*(2*(CB*mb)))) (Fin (2*(2*(2*(Co*ma)))) × Fin (1*(2*(CB*mb)))) ℂ :=
  g72gk2_kj g72gk2_Vq (1 : Matrix (Fin (2*(2*(Co*ma))) × Fin (2*(CB*mb))) (Fin (2*(2*(Co*ma))) × Fin (2*(CB*mb))) ℂ)
def g72gk2_R6 : Matrix (Fin ((2*(2*Co))*ma) × Fin ((2*(2*CB))*mb)) (Fin (1*(2*(2*(Co*ma)))) × Fin (2*(2*(CB*mb)))) ℂ :=
  g72gk2_lk (g72gk2_sf g72gk2_gA6 (fun _ => 1)) g72gk2_B6

lemma g72gk2_gA6_iA6 (i : Fin ((2*(2*Co))*ma)) : g72gk2_gA6 (g72gk2_iA6 i) = i := by
  obtain ⟨i1, an, rfl⟩ := g72gk2_join_surj i
  obtain ⟨o1, i1, rfl⟩ := g72gk2_join_surj i1
  obtain ⟨o2, co, rfl⟩ := g72gk2_join_surj i1
  simp [g72gk2_gA6, g72gk2_iA6]

lemma g72gk2_R6_app {γ : Type*} (X : Matrix (Fin (1*(2*(2*(Co*ma)))) × Fin (2*(2*(CB*mb)))) γ ℂ) i k :
      (g72gk2_R6 (Co := Co) (CB := CB) (ma := ma) (mb := mb) * X) i k =
        ∑ j, g72gk2_B6 i.2 j * X (g72gk2_iA6 i.1, j) k := by
  simp only [g72gk2_R6, Matrix.mul_apply, Fintype.sum_prod_type, g72gk2_lk, g72gk2_sf]
  rw [Finset.sum_eq_single (g72gk2_iA6 i.1)]
  · simp only [if_pos (g72gk2_gA6_iA6 i.1), one_mul]
  · intro b _ hb
    rw [Finset.sum_eq_zero]; intro j _; rw [if_neg, zero_mul, zero_mul]
    intro h; apply hb; rw [← h]
    obtain ⟨u, b, rfl⟩ := g72gk2_join_surj b
    obtain ⟨o1, b, rfl⟩ := g72gk2_join_surj b
    obtain ⟨o2, b, rfl⟩ := g72gk2_join_surj b
    obtain ⟨co, an, rfl⟩ := g72gk2_join_surj b
    simp [g72gk2_gA6, g72gk2_iA6, Fin.fin_one_eq_zero u]
  · simp

def g72gk2_iA4 : Fin (2*(2*(2*(Co*ma)))) → Fin (2*(2*(2*(Co*ma)))) := fun k =>
  joinRegisters ((split k).1 + (split (split k).2).1) (split k).2

lemma g72gk2_R4_app {γ : Type*} (X : Matrix (Fin (2*(2*(2*(Co*ma)))) × Fin (2*(CB*mb))) γ ℂ) i k :
    (g72gk2_R4 (Co := Co) (CB := CB) (ma := ma) (mb := mb) * X) i k =
      g72gk2_sA4 (g72gk2_iA4 i.1) * X (g72gk2_iA4 i.1, (split i.2).2) k := by
  unfold g72gk2_R4
  rw [g72gk2_lk_sf, g72gk2_sfb_mul _ _ (Prod.map g72gk2_iA4 (fun i => (split i).2))]
  · simp only [mul_one, one_mul]; rfl
  · rintro ⟨j1, j2⟩
    obtain ⟨e, j1, rfl⟩ := g72gk2_join_surj j1
    obtain ⟨x1, r, rfl⟩ := g72gk2_join_surj j1
    simp [g72gk2_iA4, g72gk2_gA4, g72gk2_f2]
  · rintro ⟨j1, j2⟩
    obtain ⟨e, j1, rfl⟩ := g72gk2_join_surj j1
    obtain ⟨x1, r, rfl⟩ := g72gk2_join_surj j1
    obtain ⟨u, y, rfl⟩ := g72gk2_join_surj j2
    simp [g72gk2_iA4, g72gk2_gA4, g72gk2_f2, Fin.fin_one_eq_zero u]

lemma g72gk2_R2_app {γ : Type*} (X : Matrix (Fin (Co*(2*(2*ma))) × Fin (CB*mb)) γ ℂ) i k :
    (g72gk2_R2 (Co := Co) (CB := CB) (ma := ma) (mb := mb) * X) i k = X (g72gk2_iA2 i.1, (split i.2).2) k := by
  unfold g72gk2_R2
  rw [g72gk2_lk_sf, g72gk2_sfb_mul _ _ (Prod.map g72gk2_iA2 (fun i => (split i).2))]
  · simp only [mul_one, one_mul]; rfl
  · rintro ⟨j1, j2⟩
    obtain ⟨co, j1, rfl⟩ := g72gk2_join_surj j1
    obtain ⟨x1, j1, rfl⟩ := g72gk2_join_surj j1
    obtain ⟨x2, an, rfl⟩ := g72gk2_join_surj j1
    simp [g72gk2_iA2, g72gk2_gA2]
  · rintro ⟨j1, j2⟩
    obtain ⟨u, j1, rfl⟩ := g72gk2_join_surj j1
    obtain ⟨x1, j1, rfl⟩ := g72gk2_join_surj j1
    obtain ⟨x2, j1, rfl⟩ := g72gk2_join_surj j1
    obtain ⟨co, an, rfl⟩ := g72gk2_join_surj j1
    obtain ⟨u', y, rfl⟩ := g72gk2_join_surj j2
    simp [g72gk2_iA2, g72gk2_gA2, Fin.fin_one_eq_zero u, Fin.fin_one_eq_zero u']

variable (C : Matrix (Fin Co × Fin CB) (Fin Ca × Fin Cb) ℂ)

def g72gk2_IH2 : Matrix (Fin (Co*(2*(2*ma))) × Fin (CB*mb)) (Fin (Ca*(2*(2*ma))) × Fin (Cb*mb)) ℂ :=
  g72gk2_kj C (1 : Matrix (Fin (2*(2*ma)) × Fin mb) (Fin (2*(2*ma)) × Fin mb) ℂ)
lemma g72gk2_Z2_app j k :
    (g72gk2_IH2 (ma := ma) (mb := mb) C * g72gk2_R0 (Ca := Ca) (Cb := Cb) (ma := ma) (mb := mb)) j k =
      g72gk2_IH2 C j (g72gk2_gA0 k.1, g72gk2_gB0 k.2) := by
  unfold g72gk2_R0; rw [g72gk2_lk_sf, g72gk2_mul_sf]; simp only [mul_one]; rfl

def g72gk2_T2 : Matrix (Fin ((2*(2*Co))*ma) × Fin ((2*(2*CB))*mb)) (Fin ((2*(2*Ca))*ma) × Fin ((1*(1*Cb))*mb)) ℂ :=
  g72gk2_kj (g72gk2_kj g72gk2_Vc (g72gk2_kj g72gk2_Vc C)) (1 : Matrix (Fin ma × Fin mb) (Fin ma × Fin mb) ℂ)

set_option maxHeartbeats 4000000 in
lemma g72gk2_p2_mat :
    g72gk2_T2 (ma := ma) (mb := mb) C = g72gk2_R6 (Co := Co) (CB := CB) (ma := ma) (mb := mb) *
      (g72gk2_R5 (Co := Co) (CB := CB) (ma := ma) (mb := mb) * (g72gk2_R4 (Co := Co) (CB := CB) (ma := ma) (mb := mb) *
      (g72gk2_R3 (Co := Co) (CB := CB) (ma := ma) (mb := mb) * (g72gk2_R2 (Co := Co) (CB := CB) (ma := ma) (mb := mb) *
      (g72gk2_IH2 (ma := ma) (mb := mb) C * g72gk2_R0 (Ca := Ca) (Cb := Cb) (ma := ma) (mb := mb)))))) := by
  funext ⟨i1, i2⟩ ⟨k1, k2⟩
  obtain ⟨i1, an, rfl⟩ := g72gk2_join_surj i1
  obtain ⟨o1, i1, rfl⟩ := g72gk2_join_surj i1
  obtain ⟨o2, co, rfl⟩ := g72gk2_join_surj i1
  obtain ⟨i2, bn, rfl⟩ := g72gk2_join_surj i2
  obtain ⟨p1, i2, rfl⟩ := g72gk2_join_surj i2
  obtain ⟨p2, cB, rfl⟩ := g72gk2_join_surj i2
  obtain ⟨k1, an', rfl⟩ := g72gk2_join_surj k1
  obtain ⟨x1, k1, rfl⟩ := g72gk2_join_surj k1
  obtain ⟨x2, ca, rfl⟩ := g72gk2_join_surj k1
  obtain ⟨k2, bn', rfl⟩ := g72gk2_join_surj k2
  obtain ⟨v1, k2, rfl⟩ := g72gk2_join_surj k2
  obtain ⟨v2, cb, rfl⟩ := g72gk2_join_surj k2
  rw [g72gk2_R6_app]
  simp only [g72gk2_iA6, g72gk2_split_join, g72gk2_sum_join]
  simp only [g72gk2_R5, g72gk2_qub_mul, g72gk2_split_join, g72gk2_R4_app, g72gk2_iA4]
  simp only [g72gk2_R3, g72gk2_ent_mul, g72gk2_split_join, g72gk2_R2_app, g72gk2_iA2, g72gk2_Z2_app]
  simp only [g72gk2_gA0, g72gk2_split_join,
    g72gk2_gB0, g72gk2_IH2, g72gk2_T2, g72gk2_kj_jj, g72gk2_B6, g72gk2_Vc, Matrix.one_apply, Prod.mk.injEq,
    g72gk2_join_inj, g72gk2_sA4]
  simp only [ite_and, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero, Fin.sum_univ_two]
  by_cases h1 : an = an'
  · subst h1
    by_cases h2 : bn = bn'
    · subst h2
      by_cases h3 : o1 = x1
      · subst h3
        by_cases h4 : o2 = x2
        · subst h4
          fin_cases o1 <;> fin_cases o2 <;> fin_cases p1 <;> fin_cases p2 <;>
            (simp [g72gk2_D, g72gk2_sg]) <;> (try ring_nf) <;> (try simp only [g72gk2_s2]) <;> (try ring_nf)
        · simp [h4, Ne.symm h4]
      · simp [h3, Ne.symm h3]
    · simp [h2, Ne.symm h2]
  · simp [h1, Ne.symm h1]
end P2

section P2b
variable {Ca Cb Co CB ma mb : ℕ}

lemma g72gk2_gA0_inj : Function.Injective (g72gk2_gA0 (Ca := Ca) (ma := ma)) := by
  refine g72gk2_inj_of_left g72gk2_iA0 (fun k => ?_)
  obtain ⟨k1, an, rfl⟩ := g72gk2_join_surj k
  obtain ⟨x1, k1, rfl⟩ := g72gk2_join_surj k1
  obtain ⟨x2, ca, rfl⟩ := g72gk2_join_surj k1
  simp [g72gk2_gA0, g72gk2_iA0]

lemma g72gk2_gB0_inj : Function.Injective (g72gk2_gB0 (Cb := Cb) (mb := mb)) := by
  refine g72gk2_inj_of_left g72gk2_iB0 (fun k => ?_)
  obtain ⟨k1, an, rfl⟩ := g72gk2_join_surj k
  obtain ⟨x1, k1, rfl⟩ := g72gk2_join_surj k1
  obtain ⟨x2, ca, rfl⟩ := g72gk2_join_surj k1
  simp [g72gk2_gB0, g72gk2_iB0, Fin.fin_one_eq_zero x1, Fin.fin_one_eq_zero x2]

lemma g72gk2_gA2_inj : Function.Injective (g72gk2_gA2 (Co := Co) (ma := ma)) := by
  refine g72gk2_inj_of_left g72gk2_iA2 (fun k => ?_)
  obtain ⟨co, j1, rfl⟩ := g72gk2_join_surj k
  obtain ⟨x1, j1, rfl⟩ := g72gk2_join_surj j1
  obtain ⟨x2, an, rfl⟩ := g72gk2_join_surj j1
  simp [g72gk2_iA2, g72gk2_gA2]

lemma g72gk2_gA4_inj : Function.Injective (g72gk2_gA4 (Co := Co) (ma := ma)) := by
  refine g72gk2_inj_of_left g72gk2_iA4 (fun k => ?_)
  obtain ⟨e, j1, rfl⟩ := g72gk2_join_surj k
  obtain ⟨x1, r, rfl⟩ := g72gk2_join_surj j1
  simp [g72gk2_iA4, g72gk2_gA4, g72gk2_f2]

lemma g72gk2_gA6_inj : Function.Injective (g72gk2_gA6 (Co := Co) (ma := ma)) := by
  refine g72gk2_inj_of_left g72gk2_iA6 (fun b => ?_)
  obtain ⟨u, b, rfl⟩ := g72gk2_join_surj b
  obtain ⟨o1, b, rfl⟩ := g72gk2_join_surj b
  obtain ⟨o2, b, rfl⟩ := g72gk2_join_surj b
  obtain ⟨co, an, rfl⟩ := g72gk2_join_surj b
  simp [g72gk2_gA6, g72gk2_iA6, Fin.fin_one_eq_zero u]

lemma g72gk2_B6_iso : (g72gk2_B6 (CB := CB) (mb := mb))ᴴ * g72gk2_B6 (CB := CB) (mb := mb) = 1 := by
  funext k k'
  obtain ⟨y, k, rfl⟩ := g72gk2_join_surj k
  obtain ⟨e, r, rfl⟩ := g72gk2_join_surj k
  obtain ⟨cB, bn, rfl⟩ := g72gk2_join_surj r
  obtain ⟨y', k', rfl⟩ := g72gk2_join_surj k'
  obtain ⟨e', r', rfl⟩ := g72gk2_join_surj k'
  obtain ⟨cB', bn', rfl⟩ := g72gk2_join_surj r'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, g72gk2_B6, g72gk2_sum_join, g72gk2_split_join,
    g72gk2_join_inj, Matrix.one_apply]
  simp only [ite_and, g72gk2_star_ite, star_zero, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
  by_cases h1 : cB = cB'
  · subst h1
    by_cases h2 : bn = bn'
    · subst h2
      fin_cases y <;> fin_cases y' <;> fin_cases e <;> fin_cases e' <;>
        simp [g72gk2_D, g72gk2_sg, Fin.sum_univ_two, g72gk2_conj_s, g72gk2_ss] <;> norm_num
    · simp [h2, Ne.symm h2]
  · simp [h1, Ne.symm h1]

lemma g72gk2_p2_step (C : Matrix (Fin Co × Fin CB) (Fin Ca × Fin Cb) ℂ) (n : Kind → ℕ)
    (hIH : ∀ ma mb, g72gk2_IS (library (idle 1 1)) (Ca*ma) (Cb*mb) (Co*ma) (CB*mb) n
      (g72gk2_kj C (1 : Matrix (Fin ma × Fin mb) (Fin ma × Fin mb) ℂ)))
    (ma mb : ℕ) :
    g72gk2_IS (library (idle 1 1)) ((2*(2*Ca))*ma) ((1*(1*Cb))*mb) ((2*(2*Co))*ma) ((2*(2*CB))*mb)
      (fun k => n k + budget 0 1 1 0 0 0 0 0 k)
      (g72gk2_kj (g72gk2_kj g72gk2_Vc (g72gk2_kj g72gk2_Vc C)) (1 : Matrix (Fin ma × Fin mb) (Fin ma × Fin mb) ℂ)) := by
  have e := g72gk2_p2_mat (ma := ma) (mb := mb) C
  unfold g72gk2_T2 at e
  rw [e]
  have h0 : g72gk2_IS (library (idle 1 1)) _ _ _ _ (fun _ => 0)
      (g72gk2_R0 (Ca := Ca) (Cb := Cb) (ma := ma) (mb := mb)) :=
    g72gk2_IS_local _ _ _ (g72gk2_sf1_iso g72gk2_gA0_inj) (g72gk2_sf1_iso g72gk2_gB0_inj) _
  have h1 : g72gk2_IS (library (idle 1 1)) _ _ _ _ n (g72gk2_IH2 (ma := ma) (mb := mb) C) := hIH (2*(2*ma)) mb
  have h2 : g72gk2_IS (library (idle 1 1)) _ _ _ _ (fun _ => 0)
      (g72gk2_R2 (Co := Co) (CB := CB) (ma := ma) (mb := mb)) :=
    g72gk2_IS_local _ _ _ (g72gk2_sf1_iso g72gk2_gA2_inj) (g72gk2_sf1_iso g72gk2_J0_inj) _
  have h3 : g72gk2_IS (library (idle 1 1)) (1*(2*(2*(Co*ma)))) (1*(CB*mb)) (2*(2*(2*(Co*ma)))) (2*(CB*mb))
      (budget 0 1 0 0 0 0 0 0) (g72gk2_R3 (Co := Co) (CB := CB) (ma := ma) (mb := mb)) :=
    g72gk2_IS_call (library (idle 1 1)) Kind.ebit g72gk2_Ve g72gk2_ent_map _ _ _ (by decide)
  have h4 : g72gk2_IS (library (idle 1 1)) _ _ _ _ (fun _ => 0)
      (g72gk2_R4 (Co := Co) (CB := CB) (ma := ma) (mb := mb)) :=
    g72gk2_IS_local _ _ _ (g72gk2_sf_iso _ _ g72gk2_gA4_inj (fun k => g72gk2_sg_abs _ _)) (g72gk2_sf1_iso g72gk2_J0_inj) _
  have h5 : g72gk2_IS (library (idle 1 1)) (2*(2*(2*(Co*ma)))) (1*(2*(CB*mb))) (1*(2*(2*(Co*ma)))) (2*(2*(CB*mb)))
      (budget 0 0 1 0 0 0 0 0) (g72gk2_R5 (Co := Co) (CB := CB) (ma := ma) (mb := mb)) :=
    g72gk2_IS_call (library (idle 1 1)) Kind.qubitF g72gk2_Vq g72gk2_qub_map _ _ _ (by decide)
  have h6 : g72gk2_IS (library (idle 1 1)) _ _ _ _ (fun _ => 0)
      (g72gk2_R6 (Co := Co) (CB := CB) (ma := ma) (mb := mb)) :=
    g72gk2_IS_local _ _ _ (g72gk2_sf1_iso g72gk2_gA6_inj) g72gk2_B6_iso _
  refine g72gk2_IS_mono (g72gk2_IS_comp (g72gk2_IS_comp (g72gk2_IS_comp (g72gk2_IS_comp (g72gk2_IS_comp
    (g72gk2_IS_comp h0 h1) h2) h3) h4) h5) h6) ?_
  intro k; cases k <;> simp [budget]

end P2b

lemma g72gk2_p2_base (ma mb : ℕ) :
    g72gk2_IS (library (idle 1 1)) (1*ma) (1*mb) (1*ma) (1*mb) (budget 0 0 0 0 0 0 0 0)
      (g72gk2_kj g72gk2_one1 (1 : Matrix (Fin ma × Fin mb) (Fin ma × Fin mb) ℂ)) := by
  have := g72gk2_IS_local (library (idle 1 1)) (1 : Matrix (Fin (1*ma)) (Fin (1*ma)) ℂ)
    (1 : Matrix (Fin (1*mb)) (Fin (1*mb)) ℂ) (by simp) (by simp) (budget 0 0 0 0 0 0 0 0)
  convert this using 1
  funext ⟨i1, i2⟩ ⟨k1, k2⟩
  obtain ⟨u1, a1, rfl⟩ := g72gk2_join_surj i1
  obtain ⟨u2, a2, rfl⟩ := g72gk2_join_surj i2
  obtain ⟨u3, a3, rfl⟩ := g72gk2_join_surj k1
  obtain ⟨u4, a4, rfl⟩ := g72gk2_join_surj k2
  simp [g72gk2_lk, g72gk2_one1, Matrix.one_apply, Fin.fin_one_eq_zero u1, Fin.fin_one_eq_zero u2,
    Fin.fin_one_eq_zero u3, Fin.fin_one_eq_zero u4, ite_and]
  split_ifs <;> simp_all

lemma g72gk2_p2_all : ∀ m ma mb, g72gk2_IS (library (idle 1 1))
    ((resourceTensorCopies (cobitChannel 2) (2*m)).ai*ma) ((resourceTensorCopies (cobitChannel 2) (2*m)).bi*mb)
    ((resourceTensorCopies (cobitChannel 2) (2*m)).ao*ma) ((resourceTensorCopies (cobitChannel 2) (2*m)).bo*mb)
    (budget 0 m m 0 0 0 0 0)
    (g72gk2_kj (g72gk2_cm (cobitChannel 2) g72gk2_Vc (2*m)) (1 : Matrix (Fin ma × Fin mb) (Fin ma × Fin mb) ℂ))
  | 0, ma, mb => g72gk2_p2_base ma mb
  | m+1, ma, mb => by
    have := g72gk2_p2_step (g72gk2_cm (cobitChannel 2) g72gk2_Vc (2*m)) (budget 0 m m 0 0 0 0 0)
      (fun ma mb => g72gk2_p2_all m ma mb) ma mb
    refine g72gk2_IS_mono this ?_
    intro k; cases k <;> simp [budget]

lemma g72gk2_part2 (m : ℕ) : Exact (idle 1 1) (budget 0 m m 0 0 0 0 0) (resourceTensorCopies (cobitChannel 2) (2*m)) :=
  g72gk2_IS_exact (g72gk2_cm_map _ _ g72gk2_cob_map (2*m)) (g72gk2_IS_unanc _ (g72gk2_p2_all m 1 1))

/-- PDF pp.1–3, supporting consequence of cobit entanglement generation, coherent
teleportation, and Eq. (1): explicit sequential startup/recycling, with zero external seed.
The forward schedule first spends one cobit to generate the startup EPR pair, then recycles
one returned pair through m coherent teleportations. The reverse schedule consumes the
m displayed EPR pairs, with no additional borrowed pairs. Exact means uniform zero error.
This supporting statement is included for the specifically requested dependency interface. -/
theorem solution :
    (∀ m : ℕ, Exact (cobitChannel 2) (budget (2*m+1) 0 0 0 0 0 0 0)
      (tensorResources (resourceTensorCopies (qubitChannel 2) m) (resourceTensorCopies (entangled 2) (m+1)))) ∧
    (∀ m : ℕ, Exact (idle 1 1) (budget 0 m m 0 0 0 0 0) (resourceTensorCopies (cobitChannel 2) (2*m))) ∧
    (∀ delta > 0, ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n ≥ n0, ∃ m eo : ℕ,
      (n : ℝ)*(1/2-delta) ≤ m ∧ (n : ℝ)*(1/2-delta) ≤ eo ∧
      Exact (cobitChannel 2) (budget n 0 0 0 0 0 0 0)
        (tensorResources (resourceTensorCopies (qubitChannel 2) m) (resourceTensorCopies (entangled 2) eo))) :=
  ⟨g72gk2_part1, g72gk2_part2, g72gk2_part3⟩
