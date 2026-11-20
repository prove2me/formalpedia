-- Prove2me | solution 1 for XorParallelRepetition.Exponential.no_embedding_iff_ordered_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:42:24.711174+00:00
-- url     : https://prove2.me/submissions/3cee300b-a61b-4a57-9682-1f989796354e

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_XorGames
import Definitions.Def_XorParallelRepetition_Exponential_Embedding
import Definitions.Def_XorParallelRepetition_Exponential_Contradiction
universe u

section
set_option autoImplicit false

open scoped ENNReal

namespace XorParallelRepetition.Dev.EmbIff

open XorParallelRepetition.Exponential


/-! ### Phases -/

section Phase

variable {p : ℕ} [hp : Fact p.Prime]

lemma omega_prim : IsPrimitiveRoot (omega p) p :=
  Complex.isPrimitiveRoot_exp p hp.out.ne_zero

lemma phase_zero' : phase p 0 = 1 := by simp [phase]

lemma phase_add' (a b : ZMod p) : phase p (a + b) = phase p a * phase p b := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  unfold phase
  rw [ZMod.val_add, ← pow_add]
  have h := (omega_prim (p := p)).pow_eq_one
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) p]
  rw [pow_add, pow_mul, h, one_pow, mul_one]

lemma phase_eq_one' {c : ZMod p} (h : phase p c = 1) : c = 0 := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  unfold phase at h
  have hd := ((omega_prim (p := p)).pow_eq_one_iff_dvd _).mp h
  rw [← ZMod.val_eq_zero]
  exact Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt c)

lemma prod_phase' {α : Type*} (s : Finset α) (f : α → ZMod p) :
    ∏ j ∈ s, phase p (f j) = phase p (∑ j ∈ s, f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phase_zero']
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, phase_add']

end Phase

/-! ### The group `G` and the subgroup `H` -/

section Group

variable {p : ℕ} {ι : Type} (Ψ : GeneralizedXorGame.{u} p ι)

abbrev G := (∀ i, FreeGroup (Ψ.Q i)) × Multiplicative (ZMod p)

def gen (w : (∀ i, Ψ.Q i) × ZMod p) : G Ψ :=
  (fun i => FreeGroup.of (w.1 i), Multiplicative.ofAdd w.2)

def H : Subgroup (G Ψ) := Subgroup.closure (gen Ψ '' Ψ.μ.support)

def genS (w : (∀ i, Ψ.Q i) × ZMod p) (b : Bool) : G Ψ :=
  if b then gen Ψ w else (gen Ψ w)⁻¹

def word {N : ℕ} (e : Fin N → (∀ i, Ψ.Q i) × ZMod p) (s : Fin N → Bool) : G Ψ :=
  (List.ofFn fun j => genS Ψ (e j) (s j)).prod

lemma word_fst {N : ℕ} (e : Fin N → (∀ i, Ψ.Q i) × ZMod p) (s : Fin N → Bool) (i : ι) :
    (word Ψ e s).1 i = FreeGroup.mk (signedWord (fun j => (e j).1 i) s) := by
  induction N with
  | zero => rfl
  | succ n ih =>
    have h := ih (fun j => e j.succ) (fun j => s j.succ)
    rw [word, List.ofFn_succ, List.prod_cons, Prod.fst_mul, Pi.mul_apply]
    rw [show (List.ofFn fun j : Fin n => genS Ψ (e j.succ) (s j.succ)).prod
        = word Ψ (fun j => e j.succ) (fun j => s j.succ) from rfl, h,
      show signedWord (fun j => (e j).1 i) s = [((e 0).1 i, s 0)] ++
        signedWord (fun j => (e j.succ).1 i) (fun j => s j.succ) from List.ofFn_succ,
      ← FreeGroup.mul_mk]
    congr 1
    cases s 0 <;> simp [genS, gen, FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]

lemma word_snd {N : ℕ} (e : Fin N → (∀ i, Ψ.Q i) × ZMod p) (s : Fin N → Bool) :
    (word Ψ e s).2 = Multiplicative.ofAdd (∑ j, signValue p (s j) * (e j).2) := by
  induction N with
  | zero => rfl
  | succ n ih =>
    have h := ih (fun j => e j.succ) (fun j => s j.succ)
    rw [word, List.ofFn_succ, List.prod_cons, Prod.snd_mul]
    rw [show (List.ofFn fun j : Fin n => genS Ψ (e j.succ) (s j.succ)).prod
        = word Ψ (fun j => e j.succ) (fun j => s j.succ) from rfl, h, Fin.sum_univ_succ,
      ofAdd_add]
    congr 1
    cases s 0 <;> simp [genS, gen, signValue]

lemma genS_mem (w : (∀ i, Ψ.Q i) × ZMod p) (hw : w ∈ Ψ.μ.support) (b : Bool) :
    genS Ψ w b ∈ H Ψ := by
  have hg : gen Ψ w ∈ H Ψ := Subgroup.subset_closure ⟨w, hw, rfl⟩
  cases b
  · exact (H Ψ).inv_mem hg
  · exact hg

lemma word_mem {N : ℕ} (e : Fin N → (∀ i, Ψ.Q i) × ZMod p) (s : Fin N → Bool)
    (he : ∀ j, e j ∈ Ψ.μ.support) : word Ψ e s ∈ H Ψ := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  exact genS_mem Ψ _ (he j) _

/-- The algebraic form of an ordered contradiction. -/
def P : Prop := ∃ c : ZMod p, c ≠ 0 ∧ ((1, Multiplicative.ofAdd c) : G Ψ) ∈ H Ψ

lemma red_nil_of_mk_eq_one {α : Type*} [DecidableEq α] {L : List (α × Bool)}
    (h : FreeGroup.mk L = 1) : FreeGroup.Red L [] := by
  have h' : FreeGroup.mk L = FreeGroup.mk [] := h
  obtain ⟨L', h1, h2⟩ := FreeGroup.Red.exact.mp h'
  rw [FreeGroup.Red.nil_iff] at h2
  subst h2
  exact h1

lemma contra_P [Fact p.Prime] {N : ℕ} (R : OrderedContradiction Ψ N) : P Ψ := by
  refine ⟨∑ j, signValue p (R.sign j) * (R.challenge j).2, ?_, ?_⟩
  · intro h0
    apply R.rhs_ne_one
    rw [prod_phase', h0, phase_zero']
  · have hm := word_mem Ψ R.challenge R.sign R.mem_support
    convert hm using 1
    refine Prod.ext ?_ ?_
    · funext i
      rw [word_fst]
      have h := FreeGroup.Red.exact.mpr ⟨[], R.word_cancels i, FreeGroup.Red.refl⟩
      exact h.symm
    · rw [word_snd]

lemma P_contra (h : P Ψ) [Fact p.Prime] : ∃ N, HasOrderedContradiction Ψ N := by
  classical
  obtain ⟨c, hc, hmem⟩ := h
  have hmem' : ((1, Multiplicative.ofAdd c) : G Ψ) ∈
      Submonoid.closure (gen Ψ '' Ψ.μ.support ∪ (gen Ψ '' Ψ.μ.support)⁻¹) := by
    rw [← Subgroup.closure_toSubmonoid]
    exact hmem
  obtain ⟨l, hl, hprod⟩ := Submonoid.exists_list_of_mem_closure hmem'
  have hj : ∀ j : Fin l.length, ∃ wb : ((∀ i, Ψ.Q i) × ZMod p) × Bool,
      wb.1 ∈ Ψ.μ.support ∧ l[j] = genS Ψ wb.1 wb.2 := by
    intro j
    rcases hl _ (List.getElem_mem j.2) with h | h
    · obtain ⟨w, hw, hw'⟩ := h
      exact ⟨(w, true), hw, by simp [genS, hw']⟩
    · obtain ⟨w, hw, hw'⟩ := Set.mem_inv.mp h
      refine ⟨(w, false), hw, ?_⟩
      simp [genS, hw']
  choose wb hwb1 hwb2 using hj
  have hword : word Ψ (fun j => (wb j).1) (fun j => (wb j).2) = (1, Multiplicative.ofAdd c) := by
    rw [word, ← hprod]
    congr 1
    refine List.ext_getElem (by simp) ?_
    intro n h1 h2
    rw [List.getElem_ofFn]
    exact (hwb2 ⟨n, h2⟩).symm
  refine ⟨l.length, ⟨OrderedContradiction.mk (fun j => (wb j).1) (fun j => (wb j).2)
    hwb1 ?_ ?_⟩⟩
  · intro h1
    apply hc
    have h2 := congrArg Prod.snd hword
    rw [word_snd] at h2
    have h3 : ∑ j, signValue p (wb j).2 * (wb j).1.2 = c := Multiplicative.ofAdd.injective h2
    rw [prod_phase', h3] at h1
    exact phase_eq_one' h1
  · intro i
    apply red_nil_of_mk_eq_one
    have h2 := congrFun (congrArg Prod.fst hword) i
    rw [word_fst] at h2
    exact h2

end Group

/-! ### An embedding forbids `P` -/

section EmbForbids

variable {p : ℕ} {ι : Type} [Fintype ι] (Ψ : GeneralizedXorGame.{u} p ι)
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

noncomputable def lift1 (E : CommutingEmbedding Ψ V) (i : ι) :
    FreeGroup (Ψ.Q i) →* unitary (V →L[ℂ] V) :=
  FreeGroup.lift (fun x => ⟨E.U i x, E.unitary_mem i x⟩)

lemma lift1_comm (E : CommutingEmbedding Ψ V) {i j : ι} (hij : i ≠ j)
    (a : FreeGroup (Ψ.Q i)) (b : FreeGroup (Ψ.Q j)) :
    Commute (lift1 Ψ E i a) (lift1 Ψ E j b) := by
  have base : ∀ x y, Commute (lift1 Ψ E i (FreeGroup.of x)) (lift1 Ψ E j (FreeGroup.of y)) := by
    intro x y
    simp only [lift1, FreeGroup.lift_apply_of]
    exact Subtype.ext (E.commute i j hij x y).eq
  have base2 : ∀ y, Commute (lift1 Ψ E i a) (lift1 Ψ E j (FreeGroup.of y)) := by
    intro y
    refine FreeGroup.induction_on a ?_ ?_ ?_ ?_
    · simp
    · intro x; exact base x y
    · intro x hx; rw [map_inv]; exact hx.inv_left
    · intro x z hx hz; rw [map_mul]; exact hx.mul_left hz
  refine FreeGroup.induction_on b ?_ ?_ ?_ ?_
  · simp
  · intro y; exact base2 y
  · intro y hy; rw [map_inv]; exact hy.inv_right
  · intro y z hy hz; rw [map_mul]; exact hy.mul_right hz

noncomputable def psi0 (E : CommutingEmbedding Ψ V) :
    (∀ i, FreeGroup (Ψ.Q i)) →* unitary (V →L[ℂ] V) :=
  MonoidHom.noncommPiCoprod (lift1 Ψ E) (fun _ _ hij => lift1_comm Ψ E hij)

lemma psi0_v_mul (E : CommutingEmbedding Ψ V) (a b : ∀ i, FreeGroup (Ψ.Q i)) :
    ((psi0 Ψ E (a * b) : unitary (V →L[ℂ] V)) : V →L[ℂ] V) E.v =
      ((psi0 Ψ E a : unitary (V →L[ℂ] V)) : V →L[ℂ] V)
        (((psi0 Ψ E b : unitary (V →L[ℂ] V)) : V →L[ℂ] V) E.v) := by
  rw [map_mul]
  rfl

variable [Fact p.Prime]

noncomputable def stab (E : CommutingEmbedding Ψ V) : Subgroup (G Ψ) where
  carrier := {g | ((psi0 Ψ E g.1 : unitary (V →L[ℂ] V)) : V →L[ℂ] V) E.v =
    phase p (Multiplicative.toAdd g.2) • E.v}
  one_mem' := by
    simp [phase_zero']
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [Prod.fst_mul, psi0_v_mul, hh, map_smul, hg, smul_smul, Prod.snd_mul, toAdd_mul,
      phase_add', mul_comm]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    rw [Prod.fst_inv]
    have h1 : E.v = ((psi0 Ψ E (g.1⁻¹ * g.1) : unitary (V →L[ℂ] V)) : V →L[ℂ] V) E.v := by
      simp
    rw [psi0_v_mul, hg, map_smul] at h1
    rw [Prod.snd_inv, toAdd_inv]
    have h2 : phase p (-Multiplicative.toAdd g.2) * phase p (Multiplicative.toAdd g.2) = 1 := by
      rw [← phase_add', neg_add_cancel, phase_zero']
    conv_rhs => rw [h1, smul_smul, h2, one_smul]

lemma gen_mem_stab (E : CommutingEmbedding Ψ V) (w : (∀ i, Ψ.Q i) × ZMod p)
    (hw : w ∈ Ψ.μ.support) : gen Ψ w ∈ stab Ψ E := by
  show ((psi0 Ψ E (fun i => FreeGroup.of (w.1 i)) : unitary (V →L[ℂ] V)) : V →L[ℂ] V) E.v =
    phase p w.2 • E.v
  rw [← E.eigen w hw]
  congr 1
  simp only [psi0, MonoidHom.noncommPiCoprod, MonoidHom.coe_mk, OneHom.coe_mk]
  exact (Finset.map_noncommProd _ _ _ (unitary (V →L[ℂ] V)).subtype).trans
    (Finset.noncommProd_congr rfl (fun i _ => by simp [lift1, FreeGroup.lift_apply_of]) _)

lemma emb_c_zero (E : CommutingEmbedding Ψ V) (c : ZMod p)
    (hc : ((1, Multiplicative.ofAdd c) : G Ψ) ∈ H Ψ) : c = 0 := by
  have hle : H Ψ ≤ stab Ψ E := by
    rw [H, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    exact gen_mem_stab Ψ E w hw
  have h := hle hc
  change ((psi0 Ψ E 1 : unitary (V →L[ℂ] V)) : V →L[ℂ] V) E.v = phase p c • E.v at h
  rw [map_one] at h
  replace h : E.v = phase p c • E.v := h
  have h0 : (1 - phase p c) • E.v = 0 := by
    rw [sub_smul, one_smul, ← h, sub_self]
  rcases smul_eq_zero.mp h0 with h1 | h1
  · exact phase_eq_one' (sub_eq_zero.mp h1).symm
  · exact absurd h1 E.v_ne_zero

lemma emb_not_P (E : CommutingEmbedding Ψ V) : ¬ P Ψ := by
  rintro ⟨c, hc, hmem⟩
  exact hc (emb_c_zero Ψ E c hmem)

end EmbForbids

/-! ### Reindexing `ℓ²` along a permutation -/

section Reindex

variable {X : Type u}

lemma memℓp_comp (σ : X ≃ X) (f : lp (fun _ : X => ℂ) 2) :
    Memℓp (fun x => f (σ x)) 2 := by
  have hf : Memℓp (f : X → ℂ) 2 := f.2
  have h2 : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  rw [memℓp_gen_iff h2] at hf ⊢
  exact σ.summable_iff.mpr hf

noncomputable def reidx (σ : X ≃ X) : lp (fun _ : X => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : X => ℂ) 2 where
  toFun f := ⟨fun x => f (σ x), memℓp_comp σ f⟩
  invFun f := ⟨fun x => f (σ.symm x), memℓp_comp σ.symm f⟩
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; simp [Pi.smul_apply]
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  norm_map' f := by
    have h2 : 0 < (2 : ℝ≥0∞).toReal := by norm_num
    simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    rw [lp.norm_eq_tsum_rpow h2, lp.norm_eq_tsum_rpow h2]
    congr 1
    exact σ.tsum_eq (fun y => ‖f y‖ ^ (2 : ℝ≥0∞).toReal)

lemma reidx_apply (σ : X ≃ X) (f : lp (fun _ : X => ℂ) 2) (x : X) :
    reidx σ f x = f (σ x) := rfl

end Reindex

/-! ### The construction: no `P` gives an embedding -/

noncomputable section Construct

open Classical

variable {p : ℕ} {ι : Type} (Ψ : GeneralizedXorGame.{u} p ι)

abbrev Cq := G Ψ ⧸ H Ψ

abbrev Vq := lp (fun _ : Cq Ψ => ℂ) 2

noncomputable def rho : G Ψ →* (Vq Ψ ≃ₗᵢ[ℂ] Vq Ψ) where
  toFun g := reidx (MulAction.toPerm g⁻¹ : Equiv.Perm (Cq Ψ))
  map_one' := by
    ext f x
    simp [reidx_apply]
  map_mul' g h := by
    ext f x
    simp [reidx_apply, LinearIsometryEquiv.mul_def, mul_smul]

lemma rho_apply (g : G Ψ) (f : Vq Ψ) (x : Cq Ψ) : rho Ψ g f x = f (g⁻¹ • x) := rfl

noncomputable def Phi : G Ψ →* (Vq Ψ →L[ℂ] Vq Ψ) :=
  (unitary (Vq Ψ →L[ℂ] Vq Ψ)).subtype.comp
    ((Unitary.linearIsometryEquiv.symm : (Vq Ψ ≃ₗᵢ[ℂ] Vq Ψ) ≃* _).toMonoidHom.comp (rho Ψ))

lemma Phi_apply (g : G Ψ) (f : Vq Ψ) : Phi Ψ g f = rho Ψ g f := rfl

lemma Phi_mem (g : G Ψ) : Phi Ψ g ∈ unitary (Vq Ψ →L[ℂ] Vq Ψ) :=
  ((Unitary.linearIsometryEquiv.symm : (Vq Ψ ≃ₗᵢ[ℂ] Vq Ψ) ≃* _) (rho Ψ g)).2

lemma rho_single (g : G Ψ) (c : Cq Ψ) :
    rho Ψ g (lp.single 2 c (1 : ℂ)) = lp.single 2 (g • c) (1 : ℂ) := by
  ext d
  rw [rho_apply, lp.single_apply, lp.single_apply]
  by_cases h : d = g • c
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne]
    intro h'
    exact h (by rw [← h', smul_inv_smul])

noncomputable def cls (a : ZMod p) : Cq Ψ :=
  QuotientGroup.mk ((1, Multiplicative.ofAdd a) : G Ψ)

lemma cls_inj (hP : ¬ P Ψ) {a b : ZMod p} (h : cls Ψ a = cls Ψ b) : a = b := by
  rw [cls, cls, QuotientGroup.eq] at h
  by_contra hab
  apply hP
  refine ⟨b - a, sub_ne_zero.mpr (Ne.symm hab), ?_⟩
  convert h using 1
  refine Prod.ext ?_ ?_
  · simp
  · simp only [Prod.snd_mul, Prod.snd_inv]
    rw [← ofAdd_neg, ← ofAdd_add, neg_add_eq_sub]

noncomputable def vec [Fact p.Prime] : Vq Ψ :=
  ∑ a : ZMod p, phase p a • lp.single 2 (cls Ψ a) (1 : ℂ)

lemma vec_ne_zero [hp : Fact p.Prime] (hP : ¬ P Ψ) : vec Ψ ≠ 0 := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  intro h0
  have h1 := congrArg (fun f : Vq Ψ => f (cls Ψ 0)) h0
  simp only [vec, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
    lp.single_apply, lp.coeFn_zero, Pi.zero_apply] at h1
  rw [Finset.sum_eq_single (0 : ZMod p)] at h1
  · simp [phase_zero'] at h1
  · intro a _ ha
    rw [Pi.single_eq_of_ne, smul_zero]
    intro h'
    exact ha (cls_inj Ψ hP h').symm
  · intro h; exact absurd (Finset.mem_univ _) h

lemma shift_cls (w : (∀ i, Ψ.Q i) × ZMod p) (hw : w ∈ Ψ.μ.support) (a : ZMod p) :
    ((fun i => FreeGroup.of (w.1 i), (1 : Multiplicative (ZMod p))) : G Ψ) • cls Ψ a =
      cls Ψ (a - w.2) := by
  have h : ((fun i => FreeGroup.of (w.1 i), (1 : Multiplicative (ZMod p))) : G Ψ) *
      (1, Multiplicative.ofAdd a) = (1, Multiplicative.ofAdd (a - w.2)) * gen Ψ w := by
    refine Prod.ext ?_ ?_
    · simp [gen]
    · simp only [Prod.snd_mul, gen, one_mul]
      rw [← ofAdd_add, sub_add_cancel]
  rw [cls, MulAction.Quotient.smul_mk, smul_eq_mul, h, cls]
  exact QuotientGroup.mk_mul_of_mem _ (Subgroup.subset_closure ⟨w, hw, rfl⟩)

def Ug (i : ι) (x : Ψ.Q i) : G Ψ :=
  MonoidHom.inl (∀ i, FreeGroup (Ψ.Q i)) (Multiplicative (ZMod p))
    (Pi.mulSingle i (FreeGroup.of x))

lemma Ug_comm {i j : ι} (hij : i ≠ j) (x : Ψ.Q i) (y : Ψ.Q j) :
    Commute (Ug Ψ i x) (Ug Ψ j y) := by
  unfold Ug
  exact (Pi.mulSingle_commute (f := fun i => FreeGroup (Ψ.Q i)) hij (FreeGroup.of x) (FreeGroup.of y)).map (MonoidHom.inl _ _)

lemma prod_Ug [Fintype ι] (x : ∀ i, Ψ.Q i) :
    Finset.univ.noncommProd (fun i => Phi Ψ (Ug Ψ i (x i)))
      (fun i _ j _ hij => (Ug_comm Ψ hij (x i) (x j)).map (Phi Ψ)) =
      Phi Ψ ((fun i => FreeGroup.of (x i), 1) : G Ψ) := by
  have h : ((fun i => FreeGroup.of (x i), 1) : G Ψ) =
      MonoidHom.inl (∀ i, FreeGroup (Ψ.Q i)) (Multiplicative (ZMod p))
        (fun i => FreeGroup.of (x i)) := rfl
  rw [h, ← Finset.noncommProd_mulSingle (fun i => FreeGroup.of (x i))]
  exact (Finset.map_noncommProd _ _ _ ((Phi Ψ).comp (MonoidHom.inl _ _))).symm

noncomputable def emb [Fintype ι] [Fact p.Prime] (hP : ¬ P Ψ) :
    CommutingEmbedding Ψ (Vq Ψ) where
  U i x := Phi Ψ (Ug Ψ i x)
  unitary_mem i x := Phi_mem Ψ _
  commute i j hij x y := (Ug_comm Ψ hij x y).map (Phi Ψ)
  v := vec Ψ
  v_ne_zero := vec_ne_zero Ψ hP
  eigen w hw := by
    rw [prod_Ug, Phi_apply, vec, map_sum]
    simp only [map_smul, rho_single, Finset.smul_sum, smul_smul]
    simp only [shift_cls Ψ w hw]
    refine Fintype.sum_equiv (Equiv.subRight w.2) _ _ (fun a => ?_)
    rw [Equiv.subRight_apply, ← phase_add', add_sub_cancel]

end Construct

end XorParallelRepetition.Dev.EmbIff

namespace XorParallelRepetition.Exponential


theorem chk_no_embedding_iff_ordered_contradiction {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι]
    (Ψ : GeneralizedXorGame.{u} p ι) :
    ¬ HasCommutingEmbedding Ψ ↔ ∃ N, HasOrderedContradiction Ψ N := by
  constructor
  · intro hne
    by_contra hc
    apply hne
    have hP : ¬ XorParallelRepetition.Dev.EmbIff.P Ψ :=
      fun h => hc (XorParallelRepetition.Dev.EmbIff.P_contra Ψ h)
    exact ⟨XorParallelRepetition.Dev.EmbIff.Vq Ψ, inferInstance, inferInstance, inferInstance,
      ⟨XorParallelRepetition.Dev.EmbIff.emb Ψ hP⟩⟩
  · rintro ⟨N, ⟨R⟩⟩ ⟨V, i1, i2, i3, ⟨E⟩⟩
    exact XorParallelRepetition.Dev.EmbIff.emb_not_P Ψ E
      (XorParallelRepetition.Dev.EmbIff.contra_P Ψ R)

end XorParallelRepetition.Exponential
end

theorem solution : type_of% @XorParallelRepetition.Exponential.chk_no_embedding_iff_ordered_contradiction := @XorParallelRepetition.Exponential.chk_no_embedding_iff_ordered_contradiction
