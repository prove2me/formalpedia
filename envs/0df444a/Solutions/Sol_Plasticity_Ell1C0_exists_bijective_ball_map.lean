-- Prove2me | solution 1 for Plasticity.Ell1C0.exists_bijective_ball_map
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-11-18T19:27:14.674999+00:00
-- url     : https://prove2.me/submissions/f5a2511c-6096-44fa-8061-6768502d9863

import Definitions.Def_Plasticity_SeqSpace
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Analysis.Real.Cardinality
import Theorems.Thm_Plasticity_Ell1C0_exists_clamp_family
import Theorems.Thm_Plasticity_SetTheory_exists_bijective_of_rank_assignment
import Theorems.Thm_Plasticity_SeqSpace_mk_c0_le_continuum

namespace Sol_Plasticity_Ell1C0_exists_bijective_ball_map
open Plasticity Filter Topology
noncomputable section

/-! ### (a) relabeling isometries -/

def relabelFun {α β : Type*} (e : α ≃ β) (p : ENNReal) [Fact (1 ≤ p)]
    (x : lp (fun _ : α => ℝ) p) : lp (fun _ : β => ℝ) p :=
  ⟨fun b => x (e.symm b), by
    have hx : Memℓp (x : ∀ _ : α, ℝ) p := x.2
    show Memℓp _ p
    rcases eq_or_ne p ⊤ with rfl | hp
    · rw [memℓp_infty_iff] at hx ⊢
      obtain ⟨C, hC⟩ := hx
      exact ⟨C, by rintro _ ⟨b, rfl⟩; exact hC ⟨e.symm b, rfl⟩⟩
    · have h0 : p ≠ 0 := by
        have := Fact.out (p := 1 ≤ p)
        intro h; rw [h] at this; simp at this
      rw [memℓp_gen_iff (ENNReal.toReal_pos h0 hp)] at hx ⊢
      exact (e.symm.summable_iff).2 hx⟩

theorem relabelFun_apply {α β : Type*} (e : α ≃ β) (p : ENNReal) [Fact (1 ≤ p)]
    (x : lp (fun _ : α => ℝ) p) (b : β) : relabelFun e p x b = x (e.symm b) := rfl

theorem relabelFun_norm {α β : Type*} (e : α ≃ β) (p : ENNReal) [Fact (1 ≤ p)]
    (x : lp (fun _ : α => ℝ) p) : ‖relabelFun e p x‖ = ‖x‖ := by
  have h0 : 0 < p := lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)
  rcases eq_or_ne p ⊤ with rfl | hp
  · rw [lp.norm_eq_ciSup, lp.norm_eq_ciSup]
    exact e.symm.iSup_comp (g := fun a => ‖x a‖)
  · rw [lp.norm_eq_tsum_rpow (ENNReal.toReal_pos h0.ne' hp), lp.norm_eq_tsum_rpow (ENNReal.toReal_pos h0.ne' hp)]
    congr 1
    exact e.symm.tsum_eq (fun a => ‖x a‖ ^ p.toReal)

def relabel {α β : Type*} (e : α ≃ β) (p : ENNReal) [Fact (1 ≤ p)] :
    lp (fun _ : α => ℝ) p ≃ₗᵢ[ℝ] lp (fun _ : β => ℝ) p where
  toFun := relabelFun e p
  invFun := relabelFun e.symm p
  map_add' x y := by ext b; rfl
  map_smul' c x := by ext b; rfl
  left_inv x := by ext a; simp [relabelFun_apply]
  right_inv x := by ext a; simp [relabelFun_apply]
  norm_map' := relabelFun_norm e p

theorem relabel_apply {α β : Type*} (e : α ≃ β) (p : ENNReal) [Fact (1 ≤ p)]
    (x : lp (fun _ : α => ℝ) p) (b : β) : relabel e p x b = x (e.symm b) := rfl

theorem relabel_mem_c0 {α β : Type*} (e : α ≃ β) (x : Linf α) (hx : x ∈ c0 α) :
    relabel e ⊤ x ∈ c0 β := by
  have h : Tendsto (fun b => x (e.symm b)) cofinite (𝓝 0) :=
    hx.comp e.symm.injective.tendsto_cofinite
  exact h

def relabelC0 {α β : Type*} (e : α ≃ β) : c0 α ≃ₗᵢ[ℝ] c0 β :=
  ((relabel e ⊤).submoduleMap (c0 α)).trans (LinearIsometryEquiv.ofEq _ _ (by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact relabel_mem_c0 e x hx
    · intro y hy
      refine ⟨(relabel e ⊤).symm y, ?_, by simp⟩
      have := relabel_mem_c0 e.symm y hy
      exact this))


/-! ### (b) the case J = ℕ × ℝ -/

abbrev J := ℕ × ℝ
abbrev I := J × ℕ
abbrev L1 := lp (fun _ : J => ℝ) 1
abbrev B := Metric.closedBall (0 : L1) 1
abbrev T := Metric.closedBall (0 : c0 I) 1

def Hfun (x : L1) (i : I) : ℝ := (2 : ℝ) ^ (-((i.2 : ℤ) + 2)) * x i.1

def ev (t : T) (i : I) : ℝ := ((t.1 : c0 I) : Linf I) i

def Sim (f g : I → ℝ) : Prop := {i | f i ≠ g i}.Finite

theorem Sim.trans {f g h : I → ℝ} (a : Sim f g) (b : Sim g h) : Sim f h :=
  (a.union b).subset (by intro i hi; by_contra hc; simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc; exact hi (hc.1.trans hc.2))

theorem Sim.symm {f g : I → ℝ} (a : Sim f g) : Sim g f :=
  a.subset (by intro i hi; exact fun h => hi h.symm)

theorem Sim.refl (f : I → ℝ) : Sim f f := by simp [Sim]

theorem D_finite (x : L1) : {j | ‖x‖ / 4 < x j}.Finite := by
  rcases eq_or_lt_of_le (norm_nonneg x) with h | h
  · have : x = 0 := norm_eq_zero.1 h.symm
    subst this
    simp
  · have hs : Summable (fun j => ‖x j‖) := by
      have := (lp.memℓp x : Memℓp (x : ∀ _ : J, ℝ) 1)
      rw [memℓp_gen_iff (by norm_num)] at this
      simpa using this
    have ht := hs.tendsto_cofinite_zero
    have hev : ∀ᶠ j in cofinite, ‖x j‖ < ‖x‖ / 4 := by
      have := (tendsto_order.1 ht).2 (‖x‖ / 4) (by linarith)
      exact this
    rw [eventually_cofinite] at hev
    refine hev.subset ?_
    intro j hj
    simp only [Set.mem_setOf_eq] at hj ⊢
    intro h2
    have : x j ≤ |x j| := le_abs_self _
    rw [Real.norm_eq_abs] at h2
    linarith

theorem Hinj (x x' : L1) (h : Sim (Hfun x) (Hfun x')) : x = x' := by
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ x' j := by
    by_contra hc; push_neg at hc; exact hne (lp.ext (funext hc))
  have hinf : Set.Infinite {i : I | Hfun x i ≠ Hfun x' i} := by
    have : Function.Injective (fun k : ℕ => ((j, k) : I)) := fun a b hab => by simpa using hab
    refine Set.infinite_of_injective_forall_mem this (fun k => ?_)
    simp only [Set.mem_setOf_eq, Hfun]
    intro hh
    have hp : (2 : ℝ) ^ (-((k : ℤ) + 2)) ≠ 0 := by positivity
    exact hj (mul_left_cancel₀ hp hh)
  exact hinf h

def rk (x : L1) : ℕ :=
  open Classical in
  if {j | ‖x‖ / 4 < x j}.Nonempty then ((D_finite x).toFinset.sup Prod.fst) + 1 else 0

theorem lt_rk {x : L1} {j : J} (hj : ‖x‖ / 4 < x j) : j.1 < rk x := by
  have hne : {j | ‖x‖ / 4 < x j}.Nonempty := ⟨j, hj⟩
  unfold rk
  rw [if_pos hne]
  have : j.1 ≤ (D_finite x).toFinset.sup Prod.fst :=
    Finset.le_sup (f := Prod.fst) ((D_finite x).mem_toFinset.2 hj)
  omega

theorem rk_zero : rk 0 = 0 := by
  unfold rk
  rw [if_neg]
  rintro ⟨j, hj⟩
  simp at hj

theorem single_coord (j0 j : J) (a : ℝ) : (lp.single 1 j0 a : L1) j = if j = j0 then a else 0 := by
  rw [lp.single_apply]
  by_cases h : j = j0
  · subst h; simp
  · simp [h]

theorem rk_half (n : ℕ) : rk ((1/2 : ℝ) • lp.single 1 ((n, (0:ℝ)) : J) (1 : ℝ) : L1) = n + 1 := by
  set x : L1 := (1/2 : ℝ) • lp.single 1 ((n, (0:ℝ)) : J) (1 : ℝ) with hx
  have hnorm : ‖x‖ = 1 / 2 := by
    rw [hx, norm_smul, lp.norm_single (by norm_num)]; norm_num
  have hcoord : ∀ j, x j = if j = ((n, (0:ℝ)) : J) then 1/2 else 0 := by
    intro j
    rw [hx, lp.coeFn_smul, Pi.smul_apply, single_coord]
    split_ifs <;> simp
  have hD : {j | ‖x‖ / 4 < x j} = {((n, (0:ℝ)) : J)} := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, hcoord, hnorm]
    split_ifs with h
    · simp [h]; norm_num
    · simp [h]; norm_num
  have hne : {j | ‖x‖ / 4 < x j}.Nonempty := by rw [hD]; exact ⟨_, rfl⟩
  unfold rk
  rw [if_pos hne]
  have : (D_finite x).toFinset = {((n, (0:ℝ)) : J)} := by
    ext j; simp [hD]
  rw [this]; simp

theorem single_mem_c0 {α : Type*} [DecidableEq α] (i : α) (a : ℝ) : (lp.single ⊤ i a : Linf α) ∈ c0 α := by
  show Tendsto (⇑(lp.single ⊤ i a : Linf α)) cofinite (𝓝 0)
  refine tendsto_const_nhds.congr' ?_
  rw [EventuallyEq, eventually_cofinite]
  refine (Set.finite_singleton i).subset ?_
  intro j hj
  by_contra hji
  apply hj
  simp only [lp.single_apply]
  rw [Pi.single_eq_of_ne hji]

theorem update_exists (t : T) (i₀ : I) (s : ℝ) (hs : |s| ≤ 1) :
    ∃ t' : T, (∀ i, i ≠ i₀ → ev t' i = ev t i) ∧ ev t' i₀ = s := by
  let u : Linf I := lp.single ⊤ i₀ (s - ev t i₀)
  have hu : u ∈ c0 I := single_mem_c0 _ _
  let t'c : c0 I := t.1 + ⟨u, hu⟩
  have hcoord : ∀ i, ((t'c : c0 I) : Linf I) i = ((t.1 : c0 I) : Linf I) i + (if i = i₀ then s - ev t i₀ else 0) := by
    intro i
    show (((t.1 : c0 I) : Linf I) + u) i = _
    rw [lp.coeFn_add, Pi.add_apply]
    congr 1
    show (lp.single ⊤ i₀ (s - ev t i₀) : Linf I) i = _
    rw [lp.single_apply]; by_cases h : i = i₀
    · subst h; simp
    · simp [h]
  have hb : ∀ i, |((t.1 : c0 I) : Linf I) i| ≤ 1 := by
    intro i
    have := lp.norm_apply_le_norm (by simp) ((t.1 : c0 I) : Linf I) i
    have h2 : ‖(t.1 : c0 I)‖ ≤ 1 := mem_closedBall_zero_iff.1 t.2
    have h3 : ‖((t.1 : c0 I) : Linf I)‖ ≤ 1 := h2
    rw [Real.norm_eq_abs] at this
    linarith
  refine ⟨⟨t'c, ?_⟩, ?_, ?_⟩
  · rw [mem_closedBall_zero_iff]
    have : ‖((t'c : c0 I) : Linf I)‖ ≤ 1 := by
      apply lp.norm_le_of_forall_le (by norm_num)
      intro i
      rw [hcoord i, Real.norm_eq_abs]
      by_cases h : i = i₀
      · subst h; simp [ev] at hs ⊢; simpa using hs
      · simp [h]; exact hb i
    exact this
  · intro i hi
    show ((t'c : c0 I) : Linf I) i = _
    rw [hcoord i]; simp [hi]; rfl
  · show ((t'c : c0 I) : Linf I) i₀ = s
    rw [hcoord i₀]; simp [ev]


def Pt : Type := {x : B // ∀ j, (x : L1) ≠ lp.single 1 j 1}

theorem ne_single_of_norm_le {x : L1} (hx : ‖x‖ ≤ 1 / 2) (j : J) : x ≠ lp.single 1 j 1 := by
  intro h
  rw [h, lp.norm_single (by norm_num)] at hx
  norm_num at hx

theorem exists_base (n : ℕ) : ∃ p : Pt, rk p.1.1 = n := by
  cases n with
  | zero =>
    refine ⟨⟨⟨0, by simp⟩, fun j => ne_single_of_norm_le (by simp) j⟩, ?_⟩
    exact rk_zero
  | succ m =>
    have hn : ‖((1/2 : ℝ) • lp.single 1 ((m, (0:ℝ)) : J) (1 : ℝ) : L1)‖ ≤ 1 / 2 := by
      rw [norm_smul, lp.norm_single (by norm_num)]; norm_num
    refine ⟨⟨⟨(1/2 : ℝ) • lp.single 1 ((m, (0:ℝ)) : J) (1 : ℝ), ?_⟩,
      fun j => ne_single_of_norm_le hn j⟩, ?_⟩
    · rw [mem_closedBall_zero_iff]; linarith
    · exact rk_half m

theorem card_I : Cardinal.mk I ≤ Cardinal.continuum := by
  simp only [I, J, Cardinal.mk_prod, Cardinal.mk_real, Cardinal.lift_id, Cardinal.mk_nat]
  have h := Cardinal.aleph0_le_continuum
  exact Cardinal.mul_le_of_le h (Cardinal.mul_le_of_le h h le_rfl) h

theorem card_T_le : Cardinal.mk T ≤ Cardinal.continuum :=
  (Cardinal.mk_set_le _).trans (SeqSpace.mk_c0_le_continuum I card_I)


open Classical in
def rho (t : T) : ℕ :=
  if h : ∃ p : Pt, Sim (ev t) (Hfun p.1.1) then rk (Classical.choose h).1.1 else 0

theorem rho_eq (t : T) (p : Pt) (h : Sim (ev t) (Hfun p.1.1)) : rho t = rk p.1.1 := by
  have hex : ∃ p : Pt, Sim (ev t) (Hfun p.1.1) := ⟨p, h⟩
  unfold rho
  rw [dif_pos hex]
  have hq := Classical.choose_spec hex
  have : (Classical.choose hex).1.1 = p.1.1 := Hinj _ _ (hq.symm.trans h)
  rw [this]

theorem core :
    ∃ F : B → T, LipschitzWith 1 F ∧ Function.Bijective F ∧
      F ⟨0, Metric.mem_closedBall_self zero_le_one⟩ = ⟨0, Metric.mem_closedBall_self zero_le_one⟩ ∧
      ∃ u : ℕ → B, ∀ m, ‖(u m : L1)‖ = 1 ∧ ‖(F (u m) : c0 I)‖ = 1 / ((m : ℝ) + 2) := by
  classical
  obtain ⟨G, h1, h2, h3, h4, h5⟩ := Ell1C0.exists_clamp_family J
  let Φ : (ℕ × ℝ → T) → Pt → T := fun y p => G y p.1
  have hsim : ∀ y (p : Pt), Sim (ev (Φ y p)) (Hfun p.1.1) := fun y p => h5 y p.1 p.2
  have hdep : ∀ y y' p, (∀ m k, m < rk p.1.1 → y (m, k) = y' (m, k)) → Φ y p = Φ y' p := by
    intro y y' p h
    exact h3 y y' p.1 (fun j hj => h j.1 j.2 (lt_rk hj))
  have hrank : ∀ y p, rho (Φ y p) = rk p.1.1 := fun y p => rho_eq _ p (hsim y p)
  have hinj : ∀ y, Function.Injective (Φ y) := by
    intro y p q hpq
    have : Sim (Hfun p.1.1) (Hfun q.1.1) := by
      have := (hsim y p).symm
      rw [hpq] at this
      exact this.trans (hsim y q)
    exact Subtype.ext (Subtype.ext (Hinj _ _ this))
  let i₀ : I := ((0, 0), 0)
  have hcard : ∀ y n, Cardinal.mk ↥({t | rho t = n} \ Φ y '' {p | rk p.1.1 = n}) = Cardinal.mk ℝ := by
    intro y n
    rw [Cardinal.mk_real]
    apply le_antisymm
    · exact (Cardinal.mk_set_le _).trans card_T_le
    · obtain ⟨p, hp⟩ := exists_base n
      let t0 := Φ y p
      have hupd : ∀ s : Set.Icc (0:ℝ) 1, ∃ t' : T, (∀ i, i ≠ i₀ → ev t' i = ev t0 i) ∧ ev t' i₀ = s :=
        fun s => update_exists t0 i₀ s (by rw [abs_of_nonneg s.2.1]; exact s.2.2)
      choose f hf1 hf2 using hupd
      have hfsim : ∀ s, Sim (ev (f s)) (Hfun p.1.1) := by
        intro s
        have : Sim (ev (f s)) (ev t0) :=
          (Set.finite_singleton i₀).subset (fun i hi => by
            by_contra hc; exact hi (hf1 s i hc))
        exact this.trans (hsim y p)
      have hfinj : Function.Injective f := by
        intro s s' h
        apply Subtype.ext
        rw [← hf2 s, ← hf2 s', h]
      have hsub : ∀ s, (∃ q, Φ y q = f s) → f s = t0 := by
        rintro s ⟨q, hq⟩
        have : Sim (Hfun q.1.1) (Hfun p.1.1) := by
          have h1' := (hsim y q).symm
          rw [hq] at h1'
          exact h1'.trans (hfsim s)
        have hqp : q = p := Subtype.ext (Subtype.ext (Hinj _ _ this))
        rw [← hq, hqp]
      let A : Set (Set.Icc (0:ℝ) 1) := {s | f s ∈ Φ y '' {p | rk p.1.1 = n}}
      have hA : A.Subsingleton := by
        intro s hs s' hs'
        obtain ⟨q, _, hq⟩ := hs
        obtain ⟨q', _, hq'⟩ := hs'
        exact hfinj ((hsub s ⟨q, hq⟩).trans (hsub s' ⟨q', hq'⟩).symm)
      have hAc : Cardinal.mk (Aᶜ : Set _) ≤ Cardinal.mk ↥({t | rho t = n} \ Φ y '' {p | rk p.1.1 = n}) := by
        refine Cardinal.mk_le_of_injective (f := fun s => (⟨f s.1, ?_, s.2⟩ : ↥({t | rho t = n} \ Φ y '' {p | rk p.1.1 = n}))) ?_
        · exact (rho_eq _ p (hfsim s.1)).trans hp
        · intro a b hab
          exact Subtype.ext (hfinj (congrArg Subtype.val hab))
      have htot := Cardinal.mk_sum_compl A
      have hIcc : Cardinal.mk (Set.Icc (0:ℝ) 1) = Cardinal.continuum := Cardinal.mk_Icc_real (by norm_num)
      rw [hIcc] at htot
      have hA1 : Cardinal.mk A ≤ 1 := Cardinal.le_one_iff_subsingleton.2 hA.coe_sort
      by_contra hlt
      push_neg at hlt
      have hlt' := lt_of_le_of_lt hAc hlt
      have := Cardinal.add_lt_of_lt Cardinal.aleph0_le_continuum
        (lt_of_le_of_lt hA1 (lt_of_lt_of_le Cardinal.one_lt_aleph0 Cardinal.aleph0_le_continuum)) hlt'
      exact absurd htot (ne_of_lt this)
  haveI : Nonempty T := ⟨⟨0, by simp⟩⟩
  obtain ⟨y, hy⟩ := SetTheory.exists_bijective_of_rank_assignment (T := T) (K := ℝ) Φ
    (fun p => rk p.1.1) rho hdep hrank hinj hcard
  let e : J → B := fun j => ⟨lp.single 1 j 1, by
    rw [mem_closedBall_zero_iff, lp.norm_single (by norm_num)]; simp⟩
  have hcase : ∀ x : B, (∃ j, (x : L1) = lp.single 1 j 1) ∨ (∀ j, (x : L1) ≠ lp.single 1 j 1) := by
    intro x
    by_cases h : ∃ j, (x : L1) = lp.single 1 j 1
    · exact Or.inl h
    · right; push_neg at h; exact h
  have hFe : ∀ j, G y (e j) = y j := fun j => h2 y j (e j) rfl
  have hFp : ∀ p : Pt, G y p.1 = Φ y p := fun p => rfl
  have hzero : G y ⟨0, Metric.mem_closedBall_self zero_le_one⟩ = ⟨0, Metric.mem_closedBall_self zero_le_one⟩ := by
    apply Subtype.ext; apply Subtype.ext; apply lp.ext; funext i
    have := h4 y ⟨0, Metric.mem_closedBall_self zero_le_one⟩ (by intro j; simp)
    rw [this i]; simp
  have hbij : Function.Bijective (G y) := by
    constructor
    · intro a b hab
      have key := hy.1
      rcases hcase a with ⟨j, hj⟩ | ha
      · have haa : a = e j := Subtype.ext hj
        rcases hcase b with ⟨j', hj'⟩ | hb
        · have hbb : b = e j' := Subtype.ext hj'
          rw [haa, hbb, hFe, hFe] at hab
          have := key (a₁ := Sum.inr j) (a₂ := Sum.inr j') (by exact hab)
          have hjj := Sum.inr.inj this
          rw [haa, hbb, hjj]
        · exfalso
          have : G y b = Φ y ⟨b, hb⟩ := rfl
          rw [haa, hFe, this] at hab
          have := key (a₁ := Sum.inr j) (a₂ := Sum.inl ⟨b, hb⟩) (by exact hab)
          cases this
      · rcases hcase b with ⟨j', hj'⟩ | hb
        · exfalso
          have hbb : b = e j' := Subtype.ext hj'
          have : G y a = Φ y ⟨a, ha⟩ := rfl
          rw [hbb, hFe, this] at hab
          have := key (a₁ := Sum.inl ⟨a, ha⟩) (a₂ := Sum.inr j') (by exact hab)
          cases this
        · have : G y a = Φ y ⟨a, ha⟩ := rfl
          have h' : G y b = Φ y ⟨b, hb⟩ := rfl
          rw [this, h'] at hab
          have := key (a₁ := Sum.inl ⟨a, ha⟩) (a₂ := Sum.inl ⟨b, hb⟩) (by exact hab)
          exact congrArg Subtype.val (Sum.inl.inj this)
    · intro t
      obtain ⟨z, hz⟩ := hy.2 t
      cases z with
      | inl p => exact ⟨p.1, by rw [hFp]; exact hz⟩
      | inr j => exact ⟨e j, by rw [hFe]; exact hz⟩
  refine ⟨G y, ?_, hbij, hzero, ?_⟩
  · exact h1 y
  · have hex : ∀ m : ℕ, ∃ t : T, (∀ i, i ≠ i₀ → ev t i = 0) ∧ ev t i₀ = 1 / ((m : ℝ) + 2) := by
      intro m
      obtain ⟨t, ht1, ht2⟩ := update_exists (⟨0, by simp⟩ : T) i₀ (1 / ((m : ℝ) + 2)) (by
        rw [abs_of_nonneg (by positivity)]
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])
      exact ⟨t, fun i hi => by rw [ht1 i hi]; rfl, ht2⟩
    choose tm htm1 htm2 using hex
    have hnorm : ∀ m, ‖(tm m : c0 I)‖ = 1 / ((m : ℝ) + 2) := by
      intro m
      apply le_antisymm
      · show ‖((tm m : c0 I) : Linf I)‖ ≤ _
        apply lp.norm_le_of_forall_le (by positivity)
        intro i
        by_cases hi : i = i₀
        · subst hi; have := htm2 m; simp only [ev] at this; rw [this, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        · have := htm1 m i hi; simp only [ev] at this; rw [this]; simp; positivity
      · have := lp.norm_apply_le_norm (by simp) ((tm m : c0 I) : Linf I) i₀
        have h2' := htm2 m; simp only [ev] at h2'
        rw [h2', Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
        exact this
    have hpre : ∀ m, ∃ x : B, (∃ j, (x : L1) = lp.single 1 j 1) ∧ G y x = tm m := by
      intro m
      obtain ⟨x, hx⟩ := hbij.2 (tm m)
      rcases hcase x with h | hx'
      · exact ⟨x, h, hx⟩
      · exfalso
        let p : Pt := ⟨x, hx'⟩
        have hpm : Sim (ev (tm m)) (Hfun p.1.1) := by
          have := hsim y p
          have e2 : Φ y p = tm m := hx
          rw [e2] at this; exact this
        have hz : Sim (ev (tm m)) (Hfun (0 : L1)) :=
          (Set.finite_singleton i₀).subset (fun i hi => by
            by_contra hc
            apply hi
            rw [htm1 m i hc]; simp [Hfun])
        have : p.1.1 = 0 := Hinj _ _ (hpm.symm.trans hz)
        have hp0 : x = ⟨0, Metric.mem_closedBall_self zero_le_one⟩ := Subtype.ext this
        rw [hp0, hzero] at hx
        have e1 : ev (tm m) i₀ = 0 := by rw [← hx]; rfl
        have hpos : (0:ℝ) < 1 / ((m:ℝ) + 2) := by positivity
        have := htm2 m
        linarith
    choose u hu1 hu2 using hpre
    refine ⟨u, fun m => ⟨?_, ?_⟩⟩
    · obtain ⟨j, hj⟩ := hu1 m
      rw [hj, lp.norm_single (by norm_num)]; simp
    · rw [hu2 m, hnorm m]


/-! ### (c) transport to Γ -/

def ballFun {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] (f : E ≃ₗᵢ[ℝ] E') (x : Metric.closedBall (0 : E) 1) :
    Metric.closedBall (0 : E') 1 :=
  ⟨f x, by rw [mem_closedBall_zero_iff, f.norm_map]; exact mem_closedBall_zero_iff.1 x.2⟩

theorem ballFun_dist {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (f : E ≃ₗᵢ[ℝ] E') (x x' : Metric.closedBall (0 : E) 1) :
    dist (ballFun f x) (ballFun f x') = dist x x' := by
  simp only [Subtype.dist_eq, ballFun, f.dist_map]

theorem ballFun_bij {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (f : E ≃ₗᵢ[ℝ] E') :
    Function.Bijective (ballFun f) := by
  constructor
  · intro x x' h
    apply Subtype.ext
    exact f.injective (congrArg Subtype.val h)
  · intro y
    refine ⟨ballFun f.symm y, ?_⟩
    apply Subtype.ext
    simp [ballFun]

theorem ballFun_zero {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (f : E ≃ₗᵢ[ℝ] E') :
    ballFun f ⟨0, Metric.mem_closedBall_self zero_le_one⟩ = ⟨0, Metric.mem_closedBall_self zero_le_one⟩ := by
  apply Subtype.ext; simp [ballFun]

theorem ballFun_norm {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (f : E ≃ₗᵢ[ℝ] E') (x : Metric.closedBall (0 : E) 1) :
    ‖(ballFun f x : E')‖ = ‖(x : E)‖ := by
  simp [ballFun]

theorem ballFun_symm_apply {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] (f : E ≃ₗᵢ[ℝ] E') (x : Metric.closedBall (0 : E) 1) :
    ballFun f (ballFun f.symm (ballFun f x)) = ballFun f x := by
  apply Subtype.ext; simp [ballFun]

theorem mk_J : Cardinal.mk J = Cardinal.continuum := by
  apply le_antisymm
  · have h := Cardinal.aleph0_le_continuum
    simp only [J, Cardinal.mk_prod, Cardinal.mk_real, Cardinal.lift_id, Cardinal.mk_nat]
    exact Cardinal.mul_le_of_le h h le_rfl
  · have : Cardinal.mk ℝ ≤ Cardinal.mk J :=
      Cardinal.mk_le_of_injective (f := fun r : ℝ => ((0, r) : J)) (fun a b h => by simpa using h)
    rwa [Cardinal.mk_real] at this

theorem mk_I' : Cardinal.mk I = Cardinal.continuum := by
  apply le_antisymm card_I
  have : Cardinal.mk J ≤ Cardinal.mk I :=
    Cardinal.mk_le_of_injective (f := fun r : J => ((r, 0) : I)) (fun a b h => by simpa using h)
  rwa [mk_J] at this

end
end Sol_Plasticity_Ell1C0_exists_bijective_ball_map

open Sol_Plasticity_Ell1C0_exists_bijective_ball_map in
theorem solution (Γ : Type*)
    (hΓ : Cardinal.mk Γ = Cardinal.continuum) :
    ∃ F : Metric.closedBall (0 : lp (fun _ : Γ => ℝ) 1) 1 → Metric.closedBall (0 : Plasticity.c0 Γ) 1,
      LipschitzWith 1 F ∧ Function.Bijective F ∧
      F ⟨0, Metric.mem_closedBall_self zero_le_one⟩ = ⟨0, Metric.mem_closedBall_self zero_le_one⟩ ∧
      ∃ u : ℕ → Metric.closedBall (0 : lp (fun _ : Γ => ℝ) 1) 1,
        ∀ m, ‖(u m : lp (fun _ : Γ => ℝ) 1)‖ = 1 ∧ ‖(F (u m) : Plasticity.c0 Γ)‖ = 1 / ((m : ℝ) + 2) := by
  obtain ⟨F, hL, hB, h0, u, hu⟩ := core
  have eJ : Nonempty (Γ ≃ J) := Cardinal.lift_mk_eq'.1 (by rw [hΓ, mk_J, Cardinal.lift_continuum, Cardinal.lift_continuum])
  have eI : Nonempty (Γ ≃ I) := Cardinal.lift_mk_eq'.1 (by rw [hΓ, mk_I', Cardinal.lift_continuum, Cardinal.lift_continuum])
  obtain ⟨eJ⟩ := eJ
  obtain ⟨eI⟩ := eI
  let Λ := relabel eJ 1
  let Ψ := relabelC0 eI
  refine ⟨ballFun Ψ.symm ∘ F ∘ ballFun Λ, ?_, ?_, ?_, fun m => ballFun Λ.symm (u m), fun m => ?_⟩
  · have h1 : LipschitzWith 1 (ballFun Λ) := (LipschitzWith.of_dist_le_mul (fun x y => by
      rw [ballFun_dist]; simp))
    have h2 : LipschitzWith 1 (ballFun Ψ.symm) := (LipschitzWith.of_dist_le_mul (fun x y => by
      rw [ballFun_dist]; simp))
    simpa using h2.comp (hL.comp h1)
  · exact (ballFun_bij Ψ.symm).comp (hB.comp (ballFun_bij Λ))
  · simp only [Function.comp]
    rw [ballFun_zero, h0, ballFun_zero]
  · have e1 : ballFun Λ (ballFun Λ.symm (u m)) = u m := by
      apply Subtype.ext; simp [ballFun]
    simp only [Function.comp]
    rw [e1, ballFun_norm, ballFun_norm]
    exact hu m
