-- Prove2me | solution 1 for SymmetricDepthHierarchy.ConstantDepth.Supplement.theorem_7_7
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T17:09:12.957006+00:00
-- url     : https://prove2.me/submissions/b583253b-8596-443f-a104-072403ac1fa0

import Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_Supplement_Joint
import Theorems.Thm_SymmetricDepthHierarchy_ConstantDepth_Supplement_proposition_7_5

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth.Supplement


section PartA
variable {K X V : Type} [Field K] [Fintype V]

lemma evalStep_equivariant (C : VariableCircuit K X V) (γ : Equiv.Perm X) (σ : Equiv.Perm V)
    (h : C.extension γ σ) (a b : V → MvPolynomial X K)
    (hab : ∀ u, MvPolynomial.rename γ (a u) = b (σ u)) (v : V) :
    MvPolynomial.rename γ (C.evalStep a v) = C.evalStep b (σ v) := by
  obtain ⟨h1, h2⟩ := h
  have hl := h2 v
  unfold VariableCircuit.evalStep
  cases hv : C.label v with
  | var x => rw [hv] at hl; simp [hl]
  | const c => rw [hv] at hl; simp [hl]
  | op o =>
    rw [hv] at hl; simp only [hl]
    cases o with
    | add =>
      simp only [map_sum, map_mul, map_natCast, hab]
      refine Eq.trans ?_ (Equiv.sum_comp σ (fun u => (C.mult (σ v) u : MvPolynomial X K) * b u))
      simp [h1]
    | mul =>
      simp only [map_prod, map_pow, hab]
      refine Eq.trans ?_ (Equiv.prod_comp σ (fun u => b u ^ C.mult (σ v) u))
      simp [h1]

lemma evalAux_equivariant (C : VariableCircuit K X V) (γ : Equiv.Perm X) (σ : Equiv.Perm V)
    (h : C.extension γ σ) (k : ℕ) (v : V) :
    MvPolynomial.rename γ (C.evalAux k v) = C.evalAux k (σ v) := by
  induction k generalizing v with
  | zero => exact evalStep_equivariant C γ σ h _ _ (by intro u; simp) v
  | succ k ih => exact evalStep_equivariant C γ σ h _ _ (fun u => ih u) v

lemma out_fixed (C : VariableCircuit K X V) (hw : C.wellFormed) (γ : Equiv.Perm X)
    (σ : Equiv.Perm V) (h : C.extension γ σ) : σ C.out = C.out := by
  obtain ⟨_, hac, _, hr⟩ := hw
  have hmap : ∀ u v, Relation.ReflTransGen C.wire u v →
      Relation.ReflTransGen C.wire (σ u) (σ v) := by
    intro u v huv
    induction huv with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hb ih =>
      refine ih.tail ?_
      unfold VariableCircuit.wire at *
      rw [h.1]; exact hb
  have h1 : Relation.ReflTransGen C.wire C.out (σ C.out) := by
    obtain ⟨u, hu⟩ := σ.surjective C.out
    have := hmap _ _ (hr u)
    rw [hu] at this
    exact (hr (σ.symm C.out)) |> fun _ => by simpa using this
  by_contra hne
  have h2 := hr (σ C.out)
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 h1 with h3 | h3
  · exact hne h3
  · rcases Relation.reflTransGen_iff_eq_or_transGen.1 h2 with h4 | h4
    · exact hne h4.symm
    · exact hac _ (h3.trans h4)

lemma polynomial_equivariant (C : VariableCircuit K X V) (hw : C.wellFormed) (γ : Equiv.Perm X)
    (σ : Equiv.Perm V) (h : C.extension γ σ) :
    MvPolynomial.rename γ C.polynomial = C.polynomial := by
  unfold VariableCircuit.polynomial
  rw [evalAux_equivariant C γ σ h, out_fixed C hw γ σ h]

end PartA


section Bool
variable {K : Type} [Field K] {n : ℕ} {Y : Type} [Fintype Y]

lemma booleanSum_invariant (g : MvPolynomial ((Fin n × Fin n) ⊕ Y) K)
    (γ : Circuit.Gamma n) (ρ : Equiv.Perm Y)
    (hg : MvPolynomial.rename (Equiv.sumCongr (matrixAction n γ) ρ) g = g) :
    MvPolynomial.rename (matrixAction n γ) (booleanSum g) = booleanSum g := by
  unfold booleanSum
  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.arrowCongr ρ (Equiv.refl Bool)) _ _ (fun e => ?_)
  conv_rhs => rw [← hg]
  simp only [MvPolynomial.coe_eval₂Hom]
  rw [MvPolynomial.eval₂_rename]
  erw [MvPolynomial.eval₂_comp_left ((MvPolynomial.rename (matrixAction n γ)).toRingHom)]
  congr 1
  · ext c; simp
  · funext x
    rcases x with ij | y
    · simp [matrixAction]
    · simp [Equiv.arrowCongr]

lemma invariant_of_symVNP {f : Family K} (hf : f ∈ symVNP K) (n : ℕ) (hn : 1 ≤ n) :
    invariant (f n) := by
  obtain ⟨q, _, c, N, h⟩ := hf
  obtain ⟨ρ, m, C, hw, hs, hb, _⟩ := h n hn
  intro γ
  obtain ⟨σ, hσ⟩ := hs γ
  have := polynomial_equivariant C hw _ σ hσ
  rw [← hb]
  exact booleanSum_invariant _ γ (ρ γ) this

end Bool



section Words
variable {K X : Type} [Field K] [Finite X]

def mono (w : List X) : X →₀ ℕ := Multiset.toFinsupp (w : Multiset X)

def prodX (w : List X) : MvPolynomial X K := (w.map MvPolynomial.X).prod

lemma mono_nil : mono ([] : List X) = 0 := by simp [mono]

lemma mono_cons (a : X) (v : List X) : mono (a :: v) = Finsupp.single a 1 + mono v := by
  unfold mono
  rw [← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add,
    Multiset.toFinsupp_singleton]

lemma prodX_eq (w : List X) : (prodX w : MvPolynomial X K) = MvPolynomial.monomial (mono w) 1 := by
  induction w with
  | nil => simp [prodX, mono_nil]
  | cons a w ih =>
    unfold prodX at *
    rw [List.map_cons, List.prod_cons, ih, mono_cons, MvPolynomial.X, MvPolynomial.monomial_mul]
    simp

lemma mono_map (g : Equiv.Perm X) (w : List X) :
    mono (w.map g) = (mono w).mapDomain g := by
  induction w with
  | nil => simp [mono_nil]
  | cons a w ih =>
    rw [List.map_cons, mono_cons, mono_cons, ih, Finsupp.mapDomain_add, Finsupp.mapDomain_single]

lemma mono_length (w : List X) : (mono w).degree = w.length := by
  induction w with
  | nil => simp [mono_nil]
  | cons a w ih =>
    rw [mono_cons, map_add, ih]; simp [add_comm]


def Wset (X : Type) [Finite X] (D : ℕ) : Finset (List X) :=
  (List.finite_length_le X D).toFinset

lemma mem_Wset {D : ℕ} {w : List X} : w ∈ Wset X D ↔ w.length ≤ D := by
  simp [Wset]

def cnt (D : ℕ) (m : X →₀ ℕ) : ℕ := ((Wset X D).filter fun w => mono w = m).card

def cc (D : ℕ) (p : MvPolynomial X K) (w : List X) : K :=
  p.coeff (mono w) / (cnt D (mono w) : K)

lemma cnt_map (D : ℕ) (g : Equiv.Perm X) (m : X →₀ ℕ) : cnt D (m.mapDomain g) = cnt D m := by
  unfold cnt
  symm
  refine Finset.card_bij (fun w _ => w.map g) ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, mem_Wset] at hw ⊢
    refine ⟨by simpa using hw.1, ?_⟩
    rw [mono_map, hw.2]
  · intro a _ b _ h
    exact List.map_injective_iff.2 g.injective h
  · intro b hb
    simp only [Finset.mem_filter, mem_Wset] at hb
    refine ⟨b.map g.symm, ?_, by simp⟩
    simp only [Finset.mem_filter, mem_Wset]
    refine ⟨by simpa using hb.1, ?_⟩
    have := mono_map g (b.map g.symm)
    simp only [List.map_map, Equiv.self_comp_symm, List.map_id] at this
    rw [hb.2] at this
    exact Finsupp.mapDomain_injective g.injective this.symm

lemma cc_map (D : ℕ) (p : MvPolynomial X K) (g : Equiv.Perm X)
    (hp : MvPolynomial.rename g p = p) (w : List X) : cc D p (w.map g) = cc D p w := by
  unfold cc
  rw [mono_map, cnt_map]
  congr 1
  conv_lhs => rw [← hp]
  exact MvPolynomial.coeff_rename_mapDomain g g.injective p _

lemma cnt_pos (D : ℕ) (m : X →₀ ℕ) (hm : m.degree ≤ D) : 0 < cnt D m := by
  unfold cnt
  apply Finset.card_pos.2
  refine ⟨(Multiset.toFinsupp.symm m).toList, ?_⟩
  have h1 : mono ((Multiset.toFinsupp.symm m).toList) = m := by
    unfold mono; simp
  simp only [Finset.mem_filter, mem_Wset]
  refine ⟨?_, h1⟩
  have := mono_length ((Multiset.toFinsupp.symm m).toList)
  rw [h1] at this; omega

lemma word_sum [CharZero K] (p : MvPolynomial X K) :
    p = ∑ w ∈ Wset X p.totalDegree, MvPolynomial.C (cc p.totalDegree p w) * prodX w := by
  set D := p.totalDegree with hD
  have h1 : ∀ w ∈ Wset X D, (MvPolynomial.C (cc D p w) * prodX w : MvPolynomial X K)
      = MvPolynomial.monomial (mono w) (cc D p w) := by
    intro w _
    rw [prodX_eq, MvPolynomial.C_mul_monomial, mul_one]
  rw [Finset.sum_congr rfl h1]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Wset X D) (t := (Wset X D).image mono)
    (g := mono) (fun w hw => Finset.mem_image_of_mem _ hw)]
  have h2 : ∀ m ∈ (Wset X D).image mono,
      ∑ w ∈ (Wset X D).filter (fun w => mono w = m),
        (MvPolynomial.monomial (mono w) (cc D p w) : MvPolynomial X K)
        = MvPolynomial.monomial m (p.coeff m) := by
    intro m hm
    obtain ⟨w0, hw0, rfl⟩ := Finset.mem_image.1 hm
    have : ∀ w ∈ (Wset X D).filter (fun w => mono w = mono w0),
        (MvPolynomial.monomial (mono w) (cc D p w) : MvPolynomial X K)
        = MvPolynomial.monomial (mono w0) (cc D p w0) := by
      intro w hw
      rw [(Finset.mem_filter.1 hw).2]
      unfold cc; rw [(Finset.mem_filter.1 hw).2]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul']
    have hpos : 0 < cnt D (mono w0) := Finset.card_pos.2 ⟨w0, Finset.mem_filter.2 ⟨hw0, rfl⟩⟩
    have hc : ((cnt D (mono w0) : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
    change (MvPolynomial.monomial (mono w0)) (cc D p w0) * ((cnt D (mono w0) : ℕ) : MvPolynomial X K) = _
    rw [← nsmul_eq_mul', ← map_nsmul]
    congr 1
    unfold cc
    rw [nsmul_eq_mul]
    field_simp
  rw [Finset.sum_congr rfl h2]
  conv_lhs => rw [p.as_sum]
  refine Finset.sum_subset ?_ ?_
  · intro m hm
    have hdeg : m.degree ≤ D := by
      have := MvPolynomial.le_totalDegree hm
      exact this
    have := cnt_pos D m hdeg
    obtain ⟨w, hw⟩ := Finset.card_pos.1 this
    exact Finset.mem_image.2 ⟨w, (Finset.mem_filter.1 hw).1, (Finset.mem_filter.1 hw).2⟩
  · intro m _ hm
    simp [MvPolynomial.mem_support_iff] at hm
    simp [hm]

end Words


section Valiant
variable {K X : Type} [Field K] (W : Finset (List X)) (L : ℕ)

abbrev UV := ↥W × Fin L
abbrev VV := Option (UV W L)

variable {W L}

def nxt (hW : ∀ w ∈ W, w.length ≤ L) (u : UV W L) : VV W L :=
  if h : u.2.val + 1 < u.1.1.length then
    some (u.1, ⟨u.2.val + 1, lt_of_lt_of_le h (hW _ u.1.2)⟩)
  else if u.2.val + 1 = u.1.1.length then none else some u

def allowed (hW : ∀ w ∈ W, w.length ≤ L) : VV W L → VV W L → Prop
  | none, none => True
  | none, some u => u.2.val = 0 ∧ u.1.1 ≠ []
  | some u, v => v = some u ∨ v = nxt hW u

lemma nxt_self (hW : ∀ w ∈ W, w.length ≤ L) (u : UV W L) (h : u.1.1.length ≤ u.2.val) :
    nxt hW u = some u := by
  unfold nxt
  rw [dif_neg (by omega), if_neg (by omega)]

lemma nxt_fst (hW : ∀ w ∈ W, w.length ≤ L) (u u' : UV W L) (h : nxt hW u = some u') :
    u'.1 = u.1 := by
  unfold nxt at h
  split_ifs at h <;>
    first
    | (simp only [Option.some.injEq] at h; subst h; rfl)
    | (exact absurd h (by simp))

lemma nxt_succ (hW : ∀ w ∈ W, w.length ≤ L) (u u' : UV W L) (h : nxt hW u = some u')
    (hu : u.2.val < u.1.1.length) : u'.2.val = u.2.val + 1 ∧ u.2.val + 1 < u.1.1.length := by
  unfold nxt at h
  split_ifs at h with h1 h2 <;>
    first
    | omega
    | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, h1⟩)
    | (exact absurd h (by simp))

lemma nxt_none (hW : ∀ w ∈ W, w.length ≤ L) (u : UV W L) (h : nxt hW u = none) :
    u.2.val + 1 = u.1.1.length := by
  unfold nxt at h
  split_ifs at h with h1 h2 <;>
    first
    | omega
    | (exact absurd h (by simp))

/-- downward induction: vertices of a class closed under `nxt` whose end is not hit are fixed -/
lemma fix_down (hW : ∀ w ∈ W, w.length ≤ L) (π : Equiv.Perm (VV W L))
    (hπ : ∀ v, allowed hW v (π v)) (cls : UV W L → Prop)
    (hcls : ∀ u u', cls u → nxt hW u = some u' → cls u')
    (hend : ∀ u, cls u → nxt hW u = none → ∀ v, π v = none → v ≠ some u) :
    ∀ u, cls u → π (some u) = some u := by
  have key : ∀ k u, u.1.1.length - u.2.val = k → cls u → π (some u) = some u := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro u hk hc
      by_contra hne
      have h1 : π (some u) = nxt hW u := by
        rcases hπ (some u) with h | h
        · exact absurd h hne
        · exact h
      by_cases hl : u.1.1.length ≤ u.2.val
      · exact hne (h1.trans (nxt_self hW u hl))
      · have hl := not_le.1 hl
        cases hn : nxt hW u with
        | none => exact hend u hc hn _ (h1.trans hn) rfl
        | some u'' =>
          have hs := nxt_succ hW u u'' hn hl
          have hf := nxt_fst hW u u'' hn
          have := ih (u''.1.1.length - u''.2.val) (by rw [hf]; omega) u'' rfl (hcls u u'' hc hn)
          rw [hn] at h1
          rw [← this] at h1
          have h3 := π.injective h1
          simp only [Option.some.injEq] at h3
          rw [h3] at hs; omega
  exact fun u hu => key _ u rfl hu


def first (w : ↥W) : VV W L := if h : 0 < L then some (w, ⟨0, h⟩) else none

def cycf (hW : ∀ w ∈ W, w.length ≤ L) (w : ↥W) : VV W L → VV W L
  | none => first w
  | some u => if u.1 = w then nxt hW u else some u

lemma first_eq (w : ↥W) (h : w.1 ≠ []) (hW : ∀ w ∈ W, w.length ≤ L) :
    ∃ u : UV W L, first w = some u ∧ u.1 = w ∧ u.2.val = 0 := by
  have hL : 0 < L := by
    have := hW _ w.2
    have : 0 < w.1.length := List.length_pos_iff.2 h
    omega
  exact ⟨(w, ⟨0, hL⟩), by simp [first, hL], rfl, rfl⟩

lemma nxt_inj (hW : ∀ w ∈ W, w.length ≤ L) (u u' : UV W L) (h1 : u.1 = u'.1)
    (h : nxt hW u = nxt hW u') : u = u' := by
  obtain ⟨w, j⟩ := u
  obtain ⟨w', j'⟩ := u'
  simp only at h1
  subst h1
  unfold nxt at h
  simp only at h
  split_ifs at h <;> simp_all [Prod.ext_iff, Fin.ext_iff] <;> omega

lemma cycf_inj (hW : ∀ w ∈ W, w.length ≤ L) (w : ↥W) (hw : w.1 ≠ []) :
    Function.Injective (cycf hW w) := by
  obtain ⟨u0, hu0, hu01, hu02⟩ := first_eq w hw hW
  have hlen : 0 < w.1.length := List.length_pos_iff.2 hw
  have hfirst : ∀ u : UV W L, u.1 = w → nxt hW u ≠ some u0 := by
    intro u hu h
    by_cases hl : u.1.1.length ≤ u.2.val
    · rw [nxt_self hW u hl] at h
      simp only [Option.some.injEq] at h
      subst h; rw [hu01] at hl; omega
    · have := nxt_succ hW u u0 h (not_le.1 hl); omega
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      exfalso
      simp only [cycf, hu0] at hab
      by_cases hb : b.1 = w
      · rw [if_pos hb] at hab; exact hfirst b hb hab.symm
      · rw [if_neg hb] at hab
        simp only [Option.some.injEq] at hab
        subst hab; exact hb hu01
  | some a =>
    cases b with
    | none =>
      exfalso
      simp only [cycf, hu0] at hab
      by_cases ha : a.1 = w
      · rw [if_pos ha] at hab; exact hfirst a ha hab
      · rw [if_neg ha] at hab
        simp only [Option.some.injEq] at hab
        subst hab; exact ha hu01
    | some b =>
      simp only [cycf] at hab
      by_cases ha : a.1 = w <;> by_cases hb : b.1 = w
      · rw [if_pos ha, if_pos hb] at hab
        rw [nxt_inj hW a b (ha.trans hb.symm) hab]
      · rw [if_pos ha, if_neg hb] at hab
        have := nxt_fst hW a b hab; exact absurd (this.trans ha) hb
      · rw [if_neg ha, if_pos hb] at hab
        have := nxt_fst hW b a hab.symm; exact absurd (this.trans hb) ha
      · rw [if_neg ha, if_neg hb] at hab
        exact congrArg some (Option.some.inj hab)


lemma classify (hW : ∀ w ∈ W, w.length ≤ L) (π : Equiv.Perm (VV W L))
    (hπ : ∀ v, allowed hW v (π v)) :
    π = 1 ∨ ∃ w : ↥W, w.1 ≠ [] ∧ ∀ v, π v = cycf hW w v := by
  by_cases h0 : π none = none
  · left
    have hfix := fix_down hW π hπ (fun _ => True) (fun _ _ _ _ => trivial) (by
      intro u _ _ v hv hvu
      have : v = none := π.injective (hv.trans h0.symm)
      rw [this] at hvu; exact absurd hvu (by simp)) 
    refine Equiv.ext fun v => ?_
    cases v with
    | none => simpa using h0
    | some u => simpa using hfix u trivial
  · right
    have hal := hπ none
    cases hp : π none with
    | none => exact absurd hp h0
    | some u0 =>
      rw [hp] at hal
      simp only [allowed] at hal
      obtain ⟨hu02, hu0ne⟩ := hal
      set w := u0.1 with hw
      refine ⟨w, hu0ne, ?_⟩
      have hlen : 0 < w.1.length := List.length_pos_iff.2 hu0ne
      have hfe : first w = some u0 := by
        obtain ⟨u1, h1, h2, h3⟩ := first_eq w hu0ne hW
        rw [h1]; congr 1
        exact Prod.ext h2 (Fin.ext (by rw [h3, hu02]))
      -- vertices of the word `w`
      have hB1 : ∀ j : ℕ, ∀ u : UV W L, u.1 = w → u.2.val = j → π (some u) = nxt hW u := by
        intro j
        induction j with
        | zero =>
          intro u hu hj
          have hue : u = u0 := Prod.ext hu (Fin.ext (by rw [hj, hu02]))
          rcases hπ (some u) with h | h
          · exfalso
            rw [hue] at h
            have := π.injective (h.trans hp.symm)
            simp at this
          · exact h
        | succ j ih =>
          intro u hu hj
          by_cases hl : u.1.1.length ≤ u.2.val
          · rcases hπ (some u) with h | h
            · rw [h, nxt_self hW u hl]
            · exact h
          · have hl := not_le.1 hl
            rcases hπ (some u) with h | h
            · exfalso
              -- the predecessor
              have hpred : ∃ u' : UV W L, u'.1 = w ∧ u'.2.val = j ∧ nxt hW u' = some u := by
                refine ⟨(w, ⟨j, by omega⟩), rfl, rfl, ?_⟩
                unfold nxt
                have : j + 1 < (w).1.length := by rw [← hu]; omega
                rw [dif_pos (by simpa using this)]
                congr 1
                exact Prod.ext hu.symm (Fin.ext (by simp [hj]))
              obtain ⟨u', hu'1, hu'2, hu'n⟩ := hpred
              have h1 := ih u' hu'1 hu'2
              rw [hu'n] at h1
              have := π.injective (h1.trans h.symm)
              simp only [Option.some.injEq] at this
              rw [this] at hu'2; omega
            · exact h
      have hB2 : ∀ u : UV W L, u.1 ≠ w → π (some u) = some u := by
        have hlast : ∃ ul : UV W L, ul.1 = w ∧ nxt hW ul = none := by
          have hL : w.1.length - 1 < L := by have := hW _ w.2; omega
          refine ⟨(w, ⟨w.1.length - 1, hL⟩), rfl, ?_⟩
          unfold nxt
          rw [dif_neg (by simp; omega), if_pos (by simp; omega)]
        obtain ⟨ul, hul1, hul⟩ := hlast
        have hπl : π (some ul) = none := by
          rw [hB1 _ ul hul1 rfl, hul]
        exact fun u hu => fix_down hW π hπ (fun u => u.1 ≠ w)
          (fun u u' hc hn => by rw [nxt_fst hW u u' hn]; exact hc)
          (by
            intro u hc _ v hv hvu
            have : v = some ul := π.injective (hv.trans hπl.symm)
            rw [this] at hvu
            simp only [Option.some.injEq] at hvu
            exact hc (hvu ▸ hul1.symm ▸ rfl)) u hu
      intro v
      cases v with
      | none => rw [hp, cycf, hfe]
      | some u =>
        simp only [cycf]
        by_cases hu : u.1 = w
        · rw [if_pos hu]; exact hB1 _ u hu rfl
        · rw [if_neg hu]; exact hB2 u hu


def lt' (w : List X) (j : ℕ) (d : MvPolynomial X K) : MvPolynomial X K :=
  match w[j]? with
  | some x => MvPolynomial.X x
  | none => d

def ent (hW : ∀ w ∈ W, w.length ≤ L) (c : List X → K) : VV W L → VV W L → MvPolynomial X K
  | none, none => MvPolynomial.C (c [])
  | none, some u => if u.2.val = 0 ∧ u.1.1 ≠ [] then MvPolynomial.C (c u.1.1) else 0
  | some u, v => if v = some u then 1 else if v = nxt hW u then lt' u.1.1 u.2.val 0 else 0

lemma ent_zero (hW : ∀ w ∈ W, w.length ≤ L) (c : List X → K) (v v' : VV W L)
    (h : ¬ allowed hW v v') : ent hW c v v' = 0 := by
  cases v with
  | none =>
    cases v' with
    | none => exact absurd trivial h
    | some u => simp only [ent]; simp only [allowed] at h; rw [if_neg h]
  | some u =>
    simp only [ent]
    rw [if_neg (fun h' => h (Or.inl h')), if_neg (fun h' => h (Or.inr h'))]

lemma prod_lt' (w : List X) : (w.map (MvPolynomial.X : X → MvPolynomial X K)).prod
    = ∏ j ∈ Finset.range w.length, lt' w j 1 := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [List.map_cons, List.prod_cons, ih, List.length_cons, Finset.prod_range_succ']
    simp [lt', mul_comm]

lemma prod_cyc (hW : ∀ w ∈ W, w.length ≤ L) (c : List X → K) (w : ↥W) (hw : w.1 ≠ []) :
    ∏ v, ent hW c v (cycf hW w v) =
      MvPolynomial.C (c w.1) * (w.1.map (MvPolynomial.X : X → MvPolynomial X K)).prod := by
  rw [Fintype.prod_option]
  obtain ⟨u0, hu0, hu01, hu02⟩ := first_eq w hw hW
  have hn : ent hW c none (cycf hW w none) = MvPolynomial.C (c w.1) := by
    simp only [cycf, hu0, ent]
    rw [if_pos ⟨hu02, by rw [hu01]; exact hw⟩, hu01]
  rw [hn]
  congr 1
  have hterm : ∀ u : UV W L, ent hW c (some u) (cycf hW w (some u)) =
      if u.1 = w then lt' w.1 u.2.val 1 else 1 := by
    intro u
    simp only [cycf]
    by_cases hu : u.1 = w
    · rw [if_pos hu, if_pos hu]
      simp only [ent]
      by_cases hl : u.1.1.length ≤ u.2.val
      · rw [nxt_self hW u hl, if_pos rfl]
        have : w.1[u.2.val]? = none := by
          rw [List.getElem?_eq_none_iff]; rw [← hu]; exact hl
        simp [lt', this]
      · have hl := not_le.1 hl
        have hne : nxt hW u ≠ some u := by
          intro h
          have := nxt_succ hW u u h hl
          omega
        rw [if_neg hne, if_pos trivial]
        rw [← hu]; simp [lt', List.getElem?_eq_getElem hl]
    · rw [if_neg hu, if_neg hu]
      simp [ent]
  simp only [hterm]
  rw [Fintype.prod_prod_type]
  have h1 : ∀ x : ↥W, (∏ j : Fin L, if x = w then lt' w.1 j.val (1 : MvPolynomial X K) else 1) =
      if x = w then ∏ j : Fin L, lt' w.1 j.val (1 : MvPolynomial X K) else 1 := by
    intro x; split_ifs <;> simp
  simp only [h1]
  rw [Finset.prod_ite_eq' Finset.univ w, if_pos (Finset.mem_univ _)]
  rw [Fin.prod_univ_eq_prod_range (fun j => lt' w.1 j (1 : MvPolynomial X K)) L, prod_lt']
  symm
  apply Finset.prod_subset
  · intro j hj
    simp only [Finset.mem_range] at hj ⊢
    have := hW _ w.2; omega
  · intro j _ hj
    simp only [Finset.mem_range, not_lt] at hj
    have : w.1[j]? = none := List.getElem?_eq_none_iff.2 hj
    simp [lt', this]


def cyc (hW : ∀ w ∈ W, w.length ≤ L) (w : ↥W) : Equiv.Perm (VV W L) :=
  if h : w.1 ≠ [] then Equiv.ofBijective (cycf hW w) (Finite.injective_iff_bijective.1 (cycf_inj hW w h))
  else 1

lemma cyc_apply (hW : ∀ w ∈ W, w.length ≤ L) (w : ↥W) (h : w.1 ≠ []) (v : VV W L) :
    cyc hW w v = cycf hW w v := by
  unfold cyc; rw [dif_pos h]; rfl

lemma allowed_cyc (hW : ∀ w ∈ W, w.length ≤ L) (w : ↥W) (h : w.1 ≠ []) (v : VV W L) :
    allowed hW v (cyc hW w v) := by
  rw [cyc_apply hW w h]
  obtain ⟨u0, hu0, hu01, hu02⟩ := first_eq w h hW
  cases v with
  | none => simp only [cycf, hu0, allowed]; exact ⟨hu02, by rw [hu01]; exact h⟩
  | some u =>
    simp only [cycf, allowed]
    by_cases hu : u.1 = w
    · rw [if_pos hu]; exact Or.inr rfl
    · rw [if_neg hu]; exact Or.inl rfl

lemma allowed_one (hW : ∀ w ∈ W, w.length ≤ L) (v : VV W L) :
    allowed hW v ((1 : Equiv.Perm (VV W L)) v) := by
  cases v with
  | none => trivial
  | some u => exact Or.inl rfl

lemma perm_ent (hW : ∀ w ∈ W, w.length ≤ L) (c : List X → K) (h0 : [] ∈ W) :
    ∑ π : Equiv.Perm (VV W L), ∏ v, ent hW c v (π v) =
      ∑ w ∈ W, MvPolynomial.C (c w) * (w.map (MvPolynomial.X : X → MvPolynomial X K)).prod := by
  rw [← Finset.sum_filter_of_ne (p := fun π : Equiv.Perm (VV W L) => ∀ v, allowed hW v (π v))]
  swap
  · intro π _ hne
    by_contra hcon
    obtain ⟨v, hv⟩ := not_forall.1 hcon
    exact hne (Finset.prod_eq_zero (Finset.mem_univ v) (ent_zero hW c _ _ hv))
  have hT : (Finset.univ.filter fun π : Equiv.Perm (VV W L) => ∀ v, allowed hW v (π v)) =
      insert 1 ((Finset.univ.filter fun w : ↥W => w.1 ≠ []).image (cyc hW)) := by
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_image]
    constructor
    · intro h
      rcases classify hW π h with h1 | ⟨w, hw, hπ⟩
      · exact Or.inl h1
      · refine Or.inr ⟨w, hw, ?_⟩
        exact Equiv.ext fun v => by rw [cyc_apply hW w hw, hπ]
    · rintro (rfl | ⟨w, hw, rfl⟩)
      · exact allowed_one hW
      · exact allowed_cyc hW w hw
  rw [hT, Finset.sum_insert, Finset.sum_image]
  · have h1 : ∏ v, ent hW c v ((1 : Equiv.Perm (VV W L)) v) = MvPolynomial.C (c []) := by
      rw [Fintype.prod_option]
      have : ∀ u : UV W L, ent hW c (some u) ((1 : Equiv.Perm (VV W L)) (some u)) = 1 := by
        intro u; simp [ent]
      simp only [this, Finset.prod_const_one, mul_one]
      simp [ent]
    have h2 : ∀ w ∈ Finset.univ.filter (fun w : ↥W => w.1 ≠ []),
        ∏ v, ent hW c v (cyc hW w v) = MvPolynomial.C (c w.1) * (w.1.map (MvPolynomial.X : X → MvPolynomial X K)).prod := by
      intro w hw
      have hw' := (Finset.mem_filter.1 hw).2
      rw [← prod_cyc hW c w hw']
      exact Finset.prod_congr rfl fun v _ => by rw [cyc_apply hW w hw']
    rw [h1, Finset.sum_congr rfl h2]
    set f : List X → MvPolynomial X K := fun w => MvPolynomial.C (c w) * (w.map (MvPolynomial.X : X → MvPolynomial X K)).prod with hf
    have h3 : ∑ w ∈ W, f w = f [] + ∑ w ∈ W, if w ≠ [] then f w else 0 := by
      have : ∀ w ∈ W, f w = (if w = [] then f w else 0) + (if w ≠ [] then f w else 0) := by
        intro w _; by_cases hw : w = [] <;> simp [hw]
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq' W [] f, if_pos h0]
    rw [h3]
    have h4 : (MvPolynomial.C (c []) : MvPolynomial X K) = f [] := by simp [hf]
    rw [h4]
    congr 1
    rw [Finset.sum_filter]
    exact (Finset.sum_coe_sort W (fun w => if w ≠ [] then f w else 0))
  · intro a ha b hb hab
    have ha' := (Finset.mem_filter.1 ha).2
    have hb' := (Finset.mem_filter.1 hb).2
    have := congrArg (fun π => π none) hab
    simp only [cyc_apply hW a ha', cyc_apply hW b hb', cycf] at this
    obtain ⟨ua, hua, hua1, _⟩ := first_eq a ha' hW
    obtain ⟨ub, hub, hub1, _⟩ := first_eq b hb' hW
    rw [hua, hub] at this
    simp only [Option.some.injEq] at this
    rw [← hua1, ← hub1, this]
  · simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
    intro w hw h
    have := congrArg (fun π => π none) h
    simp only [cyc_apply hW w hw, cycf] at this
    obtain ⟨u, hu, _⟩ := first_eq w hw hW
    rw [hu] at this
    simp at this


/-! ### Equivariance -/

def lmap (g : Equiv.Perm X) : List X ≃ List X where
  toFun := List.map g
  invFun := List.map g.symm
  left_inv l := by simp
  right_inv l := by simp

def sU (g : Equiv.Perm X) (hg : ∀ w, w ∈ W ↔ lmap g w ∈ W) : UV W L ≃ UV W L :=
  Equiv.prodCongr (Equiv.subtypeEquiv (lmap g) hg) (Equiv.refl _)

def sV (g : Equiv.Perm X) (hg : ∀ w, w ∈ W ↔ lmap g w ∈ W) : Equiv.Perm (VV W L) :=
  Equiv.optionCongr (sU g hg)

lemma sU_fst (g : Equiv.Perm X) (hg : ∀ w, w ∈ W ↔ lmap g w ∈ W) (u : UV W L) :
    (sU g hg u).1.1 = u.1.1.map g := rfl

lemma sU_snd (g : Equiv.Perm X) (hg : ∀ w, w ∈ W ↔ lmap g w ∈ W) (u : UV W L) :
    (sU g hg u).2 = u.2 := rfl

lemma nxt_map (hW : ∀ w ∈ W, w.length ≤ L) (g : Equiv.Perm X) (hg : ∀ w, w ∈ W ↔ lmap g w ∈ W)
    (u : UV W L) : nxt hW (sU g hg u) = Option.map (sU g hg) (nxt hW u) := by
  obtain ⟨⟨w, hw⟩, j⟩ := u
  unfold nxt
  simp only [sU_fst, sU_snd, List.length_map]
  split_ifs <;> simp [sU, lmap]


lemma lt'_map (g : Equiv.Perm X) (w : List X) (j : ℕ) :
    lt' (w.map g) j (0 : MvPolynomial X K) = MvPolynomial.rename g (lt' w j 0) := by
  unfold lt'
  rw [List.getElem?_map]
  cases w[j]? <;> simp

lemma ent_equivar (hW : ∀ w ∈ W, w.length ≤ L) (g : Equiv.Perm X)
    (hg : ∀ w, w ∈ W ↔ lmap g w ∈ W) (c : List X → K) (hc : ∀ w, c (w.map g) = c w)
    (v v' : VV W L) :
    ent hW c (sV g hg v) (sV g hg v') = MvPolynomial.rename g (ent hW c v v') := by
  cases v with
  | none =>
    cases v' with
    | none => simp [sV, ent, hc]
    | some u =>
      simp only [sV, Equiv.optionCongr_apply, Option.map_some, ent, Option.map_none]
      simp only [sU_fst, sU_snd]
      by_cases hh : u.2.val = 0 ∧ u.1.1 ≠ []
      · have hh' : u.2.val = 0 ∧ u.1.1.map g ≠ [] := by simpa using hh
        simp only [hh', hh, and_self, ne_eq, not_false_eq_true, if_true, MvPolynomial.rename_C, hc] <;> simp [hh, hh', hc]
      · have hh' : ¬ (u.2.val = 0 ∧ u.1.1.map g ≠ []) := by simpa using hh
        simp [hh, hh']
  | some u =>
    simp only [sV, Equiv.optionCongr_apply, Option.map_some, ent]
    have hinj : ∀ a b : VV W L, Option.map (sU g hg) a = Option.map (sU g hg) b ↔ a = b :=
      fun a b => (Option.map_injective (sU g hg).injective).eq_iff
    have c1 : Option.map (sU g hg) v' = some (sU g hg u) ↔ v' = some u := by
      rw [← Option.map_some]; exact hinj _ _
    have c2 : Option.map (sU g hg) v' = nxt hW (sU g hg u) ↔ v' = nxt hW u := by
      rw [nxt_map]; exact hinj _ _
    simp only [c1, c2, sU_fst, sU_snd]
    by_cases h1 : v' = some u
    · simp [h1]
    · by_cases h2 : v' = nxt hW u
      · subst h2; simp [h1, lt'_map]
      · simp [h1, h2]

end Valiant


lemma perm_fin {K X : Type} [Field K] {W : Finset (List X)} {L : ℕ} (hW : ∀ w ∈ W, w.length ≤ L)
    (c : List X → K) (h0 : [] ∈ W) {m : ℕ} (e : VV W L ≃ Fin m) :
    permanent (fun i j => ent hW c (e.symm i) (e.symm j)) =
      ∑ w ∈ W, MvPolynomial.C (c w) * (w.map (MvPolynomial.X : X → MvPolynomial X K)).prod := by
  rw [← perm_ent hW c h0]
  have key : ∀ π : Equiv.Perm (Fin m), (∏ i, ent hW c (e.symm i) (e.symm (π i))) =
      ∏ v, ent hW c v ((e.symm.permCongr π) v) := by
    intro π
    refine Fintype.prod_equiv e.symm _ _ (fun i => ?_)
    simp [Equiv.permCongr_apply]
  have key2 := Fintype.sum_equiv (e.symm.permCongr)
    (fun π : Equiv.Perm (Fin m) => ∏ i, ent hW c (e.symm i) (e.symm (π i)))
    (fun τ : Equiv.Perm (VV W L) => ∏ v, ent hW c v (τ v)) key
  unfold permanent
  convert key2


section Final
variable {K : Type} [Field K] {X : Type} [Fintype X]

def affC (r : K) : BorderDiffEq.AffineForm K X := ⟨r, fun _ => 0⟩
def affX (x : X) : BorderDiffEq.AffineForm K X := ⟨0, fun l => if l = x then 1 else 0⟩

lemma toPoly_affC (r : K) : (affC r : BorderDiffEq.AffineForm K X).toPoly = MvPolynomial.C r := by
  simp [affC, BorderDiffEq.AffineForm.toPoly]

lemma toPoly_affX (x : X) : (affX x : BorderDiffEq.AffineForm K X).toPoly = MvPolynomial.X x := by
  simp [affX, BorderDiffEq.AffineForm.toPoly]

variable {W : Finset (List X)} {L : ℕ}

def ltA (w : List X) (j : ℕ) : BorderDiffEq.AffineForm K X :=
  match w[j]? with
  | some x => affX x
  | none => affC 0

def entA (hW : ∀ w ∈ W, w.length ≤ L) (c : List X → K) : VV W L → VV W L → BorderDiffEq.AffineForm K X
  | none, none => affC (c [])
  | none, some u => if u.2.val = 0 ∧ u.1.1 ≠ [] then affC (c u.1.1) else affC 0
  | some u, v => if v = some u then affC 1 else if v = nxt hW u then ltA u.1.1 u.2.val else affC 0

lemma toPoly_entA (hW : ∀ w ∈ W, w.length ≤ L) (c : List X → K) (v v' : VV W L) :
    (entA hW c v v').toPoly = ent hW c v v' := by
  cases v with
  | none =>
    cases v' with
    | none => simp [entA, ent, toPoly_affC]
    | some u => simp only [entA, ent]; split_ifs <;> simp [toPoly_affC]
  | some u =>
    simp only [entA, ent]
    split_ifs
    · simp [toPoly_affC]
    · unfold ltA lt'; cases u.1.1[u.2.val]? <;> simp [toPoly_affX, toPoly_affC]
    · simp [toPoly_affC]

theorem proj_of_invariant [CharZero K] {n : ℕ} (p : MvPolynomial (Fin n × Fin n) K)
    (hp : invariant p) : symmetricProjection p := by
  set D := p.totalDegree with hD
  have hW : ∀ w ∈ Wset (Fin n × Fin n) D, w.length ≤ D := fun w hw => mem_Wset.1 hw
  have h0 : ([] : List (Fin n × Fin n)) ∈ Wset (Fin n × Fin n) D := mem_Wset.2 (by simp)
  let e : VV (Wset (Fin n × Fin n) D) D ≃ Fin (Fintype.card (VV (Wset (Fin n × Fin n) D) D)) :=
    Fintype.equivFin _
  refine ⟨Fintype.card (VV (Wset (Fin n × Fin n) D) D), Fintype.card_pos_iff.2 ⟨none⟩, 
    fun i j => entA hW (cc D p) (e.symm i) (e.symm j), ?_, ?_⟩
  · simp only [toPoly_entA]
    rw [perm_fin hW (cc D p) h0 e]
    exact (word_sum p).symm
  · intro γ
    set g : Equiv.Perm (Fin n × Fin n) := matrixAction n γ with hg0
    have hg : ∀ w, w ∈ Wset (Fin n × Fin n) D ↔ lmap g w ∈ Wset (Fin n × Fin n) D := by
      intro w; rw [mem_Wset, mem_Wset]; simp [lmap]
    have hpg : MvPolynomial.rename g p = p := hp γ
    have hc : ∀ w, cc D p (w.map g) = cc D p w := fun w => cc_map D p g hpg w
    refine ⟨e.symm.trans ((sV g hg).trans e), e.symm.trans ((sV g hg).trans e), fun i j => ?_⟩
    simp only [toPoly_entA, Equiv.trans_apply, Equiv.symm_apply_apply]
    exact ent_equivar hW g hg (cc D p) hc _ _

end Final

end SymmetricDepthHierarchy.ConstantDepth.Supplement

theorem solution (K : Type) [Field K] [CharZero K] :
    SymmetricDepthHierarchy.ConstantDepth.Supplement.permanentFamily K ∈
        SymmetricDepthHierarchy.ConstantDepth.Supplement.symVNP K ∧
    ∀ f : SymmetricDepthHierarchy.ConstantDepth.Supplement.Family K,
      f ∈ SymmetricDepthHierarchy.ConstantDepth.Supplement.symVNP K → ∀ n, 1 ≤ n →
        SymmetricDepthHierarchy.ConstantDepth.Supplement.symmetricProjection (f n) :=
  ⟨SymmetricDepthHierarchy.ConstantDepth.Supplement.proposition_7_5 K,
    fun f hf n hn => SymmetricDepthHierarchy.ConstantDepth.Supplement.proj_of_invariant (f n)
      (SymmetricDepthHierarchy.ConstantDepth.Supplement.invariant_of_symVNP hf n hn)⟩
