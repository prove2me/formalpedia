-- Prove2me | solution 1 for PrivPCP.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T00:39:36.549664+00:00
-- url     : https://prove2.me/submissions/e4b17391-57eb-4113-8642-e77eb8f5ac17

import Mathlib
import Definitions.Def_PrivPCP_NestedCodes


namespace PrivPCP.TDual

open GoodQLTC Classical

variable {F : Type} [Field F]

lemma mem_dualCode {α : Type} [Fintype α] (U : Submodule F (α → F)) (y : α → F) :
    y ∈ dualCode U ↔ ∀ x ∈ U, x ⬝ᵥ y = 0 := Iff.rfl

theorem dualCode_dualCode {α : Type} [Fintype α] (U : Submodule F (α → F)) :
    dualCode (dualCode U) = U := by
  ext v
  rw [mem_dualCode]
  constructor
  · intro h
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
    intro φ hφ
    set y : α → F := (dotProductEquiv F α).symm φ with hy
    have hφy : ∀ w, φ w = y ⬝ᵥ w := by
      intro w
      have : φ = dotProductEquiv F α y := by rw [hy, LinearEquiv.apply_symm_apply]
      rw [this]; rfl
    rw [hφy]
    have hyU : y ∈ dualCode U := by
      intro u hu
      rw [dotProduct_comm, ← hφy]
      exact (Submodule.mem_dualAnnihilator φ).1 hφ u hu
    exact h y hyU
  · intro hv y hy
    rw [dotProduct_comm]
    exact hy v hv

lemma dualCode_antitone {α : Type} [Fintype α] {U U' : Submodule F (α → F)} (h : U ≤ U') :
    dualCode U' ≤ dualCode U := fun y hy x hx => hy x (h hx)

theorem dualCode_iSup {α ι : Type} [Fintype α] (A : ι → Submodule F (α → F)) :
    dualCode (⨆ i, A i) = ⨅ i, dualCode (A i) := by
  apply le_antisymm
  · exact le_iInf fun i => dualCode_antitone (le_iSup A i)
  · intro y hy x hx
    rw [Submodule.mem_iInf] at hy
    refine Submodule.iSup_induction A (motive := fun x => x ⬝ᵥ y = 0) hx ?_ ?_ ?_
    · intro i x hx; exact hy i x hx
    · exact zero_dotProduct y
    · intro x x' h1 h2; rw [add_dotProduct, h1, h2, add_zero]

theorem dualCode_iInf {α ι : Type} [Fintype α] (A : ι → Submodule F (α → F)) :
    dualCode (⨅ i, A i) = ⨆ i, dualCode (A i) := by
  have : (⨅ i, A i) = dualCode (⨆ i, dualCode (A i)) := by
    rw [dualCode_iSup]; simp_rw [dualCode_dualCode]
  rw [this, dualCode_dualCode]

variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]

lemma mem_axisCode_iff (C : ∀ i, Submodule F (S i → F)) (i : ι) (x : (∀ i, S i) → F) :
    x ∈ axisCode C i ↔ ∀ b : (∀ i, S i), (fun t => x (Function.update b i t)) ∈ C i := by
  simp only [axisCode, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.funLeft_apply]
  exact Iff.rfl

/-- sum over a line -/
lemma sum_fiber_line (i : ι) (t0 : S i) (b : ∀ i, S i) (hb : b i = t0) (f : (∀ i, S i) → F) :
    ∑ ω ∈ Finset.univ.filter (fun ω => Function.update ω i t0 = b), f ω =
      ∑ t, f (Function.update b i t) := by
  symm
  refine Finset.sum_nbij' (fun t => Function.update b i t) (fun ω => ω i) ?_ ?_ ?_ ?_ ?_
  · intro t _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Function.update_idem, ← hb, Function.update_eq_self]
  · intro ω _; exact Finset.mem_univ _
  · intro t _; exact Function.update_self i t b
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    rw [← hω, Function.update_idem, Function.update_eq_self]
  · intro t _; rfl

lemma sum_by_lines (i : ι) (t0 : S i) (f : (∀ i, S i) → F) :
    ∑ ω, f ω = ∑ b, ∑ ω ∈ Finset.univ.filter (fun ω => Function.update ω i t0 = b), f ω :=
  (Finset.sum_fiberwise Finset.univ _ f).symm

theorem dualCode_axisCode (C : ∀ i, Submodule F (S i → F)) (i : ι) :
    dualCode (axisCode C i) = axisCode (fun j => dualCode (C j)) i := by
  by_cases hS : IsEmpty (S i)
  · -- the grid is empty: both sides are everything
    have hΩ : IsEmpty (∀ i, S i) := ⟨fun ω => hS.false (ω i)⟩
    ext y
    constructor
    · intro _; rw [mem_axisCode_iff]; intro b; exact (hΩ.false b).elim
    · intro _ x _; simp [dotProduct, Finset.univ_eq_empty]
  rw [not_isEmpty_iff] at hS
  obtain ⟨t0⟩ := hS
  ext y
  rw [mem_axisCode_iff]
  constructor
  · intro hy b c hc
    -- place `c` on the line through `b`
    set b' := Function.update b i t0
    let P : (∀ i, S i) → F := fun ω => if Function.update ω i t0 = b' then c (ω i) else 0
    have hP : P ∈ axisCode C i := by
      rw [mem_axisCode_iff]
      intro b''
      have : (fun t => P (Function.update b'' i t)) =
          if Function.update b'' i t0 = b' then c else 0 := by
        funext t
        simp only [P, Function.update_idem, Function.update_self]
        split_ifs <;> rfl
      rw [this]; split_ifs
      · exact hc
      · exact (C i).zero_mem
    have h0 := hy P hP
    rw [dotProduct, sum_by_lines i t0] at h0
    rw [Finset.sum_eq_single b'] at h0
    · rw [sum_fiber_line i t0 b' (by simp [b'])] at h0
      simp only [P, Function.update_idem, Function.update_self, if_true] at h0
      rw [dotProduct]
      simpa [b', Function.update_idem] using h0
    · intro b0 _ hb0
      refine Finset.sum_eq_zero fun ω hω => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      simp [P, hω, hb0]
    · simp
  · intro hy x hx
    rw [mem_axisCode_iff] at hx
    rw [dotProduct, sum_by_lines i t0]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : b i = t0
    · rw [sum_fiber_line i t0 b hb]
      exact hy b (fun t => x (Function.update b i t)) (hx b)
    · refine Finset.sum_eq_zero fun ω hω => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
      exact absurd (by rw [← hω, Function.update_self]) hb

theorem dualCode_tensorCode (V : ∀ i, Submodule F (S i → F)) :
    dualCode (tensorCode V) = ⨆ i, axisCode (fun j => dualCode (V j)) i := by
  unfold tensorCode
  rw [dualCode_iInf]
  simp_rw [dualCode_axisCode]

end PrivPCP.TDual


namespace PrivPCP.L46Aux

open GoodQLTC Classical PrivPCP.TDual

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]

abbrev Om (S : ι → Type) (I : Finset ι) : Type := ∀ i : {i // i ∈ I}, S i.val

/-- glue a value at `t` with a word on `I \ {t}` -/
def ext {I : Finset ι} {t : ι} (ht : t ∈ I) (x : S t) (y : Om S (I.erase t)) : Om S I :=
  fun i => if h : i.val = t then cast (congrArg S h.symm) x
    else y ⟨i.val, Finset.mem_erase.2 ⟨h, i.2⟩⟩

def res {I : Finset ι} {t : ι} (ht : t ∈ I) (ω : Om S I) : Om S (I.erase t) :=
  fun j => ω ⟨j.val, Finset.mem_of_mem_erase j.2⟩

abbrev tpt {I : Finset ι} {t : ι} (ht : t ∈ I) : {i // i ∈ I} := ⟨t, ht⟩

lemma ext_at {I : Finset ι} {t : ι} (ht : t ∈ I) (x : S t) (y : Om S (I.erase t)) :
    ext ht x y (tpt ht) = x := by
  unfold ext tpt
  rw [dif_pos rfl]
  rfl

lemma ext_ne {I : Finset ι} {t : ι} (ht : t ∈ I) (x : S t) (y : Om S (I.erase t))
    (i : {i // i ∈ I}) (h : i.val ≠ t) :
    ext ht x y i = y ⟨i.val, Finset.mem_erase.2 ⟨h, i.2⟩⟩ := by
  unfold ext
  rw [dif_neg h]

lemma res_ext {I : Finset ι} {t : ι} (ht : t ∈ I) (x : S t) (y : Om S (I.erase t)) :
    res ht (ext ht x y) = y := by
  funext j
  simp only [res]
  rw [ext_ne ht x y _ (Finset.ne_of_mem_erase j.2)]

lemma ext_res {I : Finset ι} {t : ι} (ht : t ∈ I) (ω : Om S I) :
    ext ht (ω (tpt ht)) (res ht ω) = ω := by
  funext i
  by_cases h : i.val = t
  · have hi : i = tpt ht := Subtype.ext h
    subst hi
    exact ext_at ht _ _
  · unfold ext; rw [dif_neg h]; rfl

lemma ext_eq_update {I : Finset ι} {t : ι} (ht : t ∈ I) (x : S t) (b : Om S I) :
    ext ht x (res ht b) = Function.update b (tpt ht) x := by
  funext i
  by_cases h : i.val = t
  · have hi : i = tpt ht := Subtype.ext h
    subst hi
    exact (ext_at ht _ _).trans (Function.update_self (tpt ht) x b).symm
  · have hne : i ≠ tpt ht := fun h' => h (congrArg Subtype.val h')
    rw [Function.update_of_ne hne]
    unfold ext; rw [dif_neg h]; rfl

lemma update_ext_ne {I : Finset ι} {t : ι} (ht : t ∈ I) (x : S t) (y : Om S (I.erase t))
    (j : {i // i ∈ I.erase t}) (s : S j.val) :
    Function.update (ext ht x y) ⟨j.val, Finset.mem_of_mem_erase j.2⟩ s =
      ext ht x (Function.update y j s) := by
  funext i
  by_cases h : i.val = t
  · have hi : i = tpt ht := Subtype.ext h
    subst hi
    have hne : (tpt ht : {i // i ∈ I}) ≠ ⟨j.val, Finset.mem_of_mem_erase j.2⟩ := by
      intro h'; exact Finset.ne_of_mem_erase j.2 (congrArg Subtype.val h').symm
    rw [Function.update_of_ne hne, ext_at, ext_at]
  · rw [ext_ne ht _ _ i h]
    by_cases hij : i.val = j.val
    · have hi : i = ⟨j.val, Finset.mem_of_mem_erase j.2⟩ := Subtype.ext hij
      subst hi
      rw [Function.update_self]
      have : (⟨j.val, Finset.mem_erase.2 ⟨h, Finset.mem_of_mem_erase j.2⟩⟩ :
        {i // i ∈ I.erase t}) = j := Subtype.ext rfl
      exact (Function.update_self j s y).symm
    · have hne : i ≠ ⟨j.val, Finset.mem_of_mem_erase j.2⟩ := fun h' => hij (congrArg Subtype.val h')
      have hne' : (⟨i.val, Finset.mem_erase.2 ⟨h, i.2⟩⟩ : {i // i ∈ I.erase t}) ≠ j :=
        fun h' => hij (congrArg Subtype.val h')
      rw [Function.update_of_ne hne, ext_ne ht _ _ i h, Function.update_of_ne hne']

/-- the gluing equivalence -/
def extEquiv {I : Finset ι} {t : ι} (ht : t ∈ I) : S t × Om S (I.erase t) ≃ Om S I where
  toFun p := ext ht p.1 p.2
  invFun ω := (ω (tpt ht), res ht ω)
  left_inv p := by simp [ext_at, res_ext]
  right_inv ω := ext_res ht ω

lemma sum_ext {I : Finset ι} {t : ι} (ht : t ∈ I) (f : Om S I → F) :
    ∑ ω, f ω = ∑ x, ∑ y, f (ext ht x y) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (extEquiv ht) _ _ (fun _ => rfl)).symm

end PrivPCP.L46Aux


namespace PrivPCP.L46Aux

open GoodQLTC Classical PrivPCP.TDual

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]

/-- contraction along coordinate `t` -/
def contr {I : Finset ι} {t : ι} (ht : t ∈ I) (v : S t → F) (Z : Om S I → F) :
    Om S (I.erase t) → F :=
  fun y => ∑ x, v x * Z (ext ht x y)

/-- tensor lift `u ⊗ P` -/
def tl {I : Finset ι} {t : ι} (ht : t ∈ I) (u : S t → F) (P : Om S (I.erase t) → F) :
    Om S I → F :=
  fun ω => u (ω (tpt ht)) * P (res ht ω)

lemma res_update_t {I : Finset ι} {t : ι} (ht : t ∈ I) (b : Om S I) (s : S t) :
    res ht (Function.update b (tpt ht) s) = res ht b := by
  rw [← ext_eq_update, res_ext]

lemma update_t_at {I : Finset ι} {t : ι} (ht : t ∈ I) (b : Om S I) (s : S t) :
    (Function.update b (tpt ht) s) (tpt ht) = s := Function.update_self _ _ _

lemma res_update_ne {I : Finset ι} {t : ι} (ht : t ∈ I) (b : Om S I)
    (j : {i // i ∈ I.erase t}) (s : S j.val) :
    res ht (Function.update b ⟨j.val, Finset.mem_of_mem_erase j.2⟩ s) =
      Function.update (res ht b) j s := by
  conv_lhs => rw [← ext_res ht b]
  rw [update_ext_ne, res_ext]

lemma update_ne_at {I : Finset ι} {t : ι} (ht : t ∈ I) (b : Om S I)
    (j : {i // i ∈ I.erase t}) (s : S j.val) :
    (Function.update b ⟨j.val, Finset.mem_of_mem_erase j.2⟩ s) (tpt ht) = b (tpt ht) := by
  apply Function.update_of_ne
  intro h
  exact Finset.ne_of_mem_erase j.2 (congrArg Subtype.val h).symm

lemma line_dot_contr {I : Finset ι} {t : ι} (ht : t ∈ I) (v : S t → F) (Z : Om S I → F)
    (b : Om S I) :
    v ⬝ᵥ (fun s => Z (Function.update b (tpt ht) s)) = contr ht v Z (res ht b) := by
  simp only [dotProduct, contr]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ext_eq_update]

lemma contr_sum {I : Finset ι} {t : ι} (ht : t ∈ I) {m : ℕ} (c : Fin m → F) (bv : Fin m → S t → F)
    (Z : Om S I → F) :
    contr ht (∑ n, c n • bv n) Z = ∑ n, c n • contr ht (bv n) Z := by
  funext y
  simp only [contr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun x _ => by ring

lemma contr_sub {I : Finset ι} {t : ι} (ht : t ∈ I) (v : S t → F) (Z Z' : Om S I → F) :
    contr ht v (Z - Z') = contr ht v Z - contr ht v Z' := by
  funext y; simp [contr, mul_sub, Finset.sum_sub_distrib]

lemma contr_fsum {I : Finset ι} {t : ι} (ht : t ∈ I) (v : S t → F) {m : ℕ}
    (Z : Fin m → Om S I → F) :
    contr ht v (∑ n, Z n) = ∑ n, contr ht v (Z n) := by
  funext y; simp only [contr, Finset.sum_apply, Finset.mul_sum]; rw [Finset.sum_comm]

lemma contr_tl {I : Finset ι} {t : ι} (ht : t ∈ I) (v u : S t → F) (P : Om S (I.erase t) → F) :
    contr ht v (tl ht u P) = (v ⬝ᵥ u) • P := by
  funext y
  simp only [contr, tl, ext_at, res_ext, Pi.smul_apply, smul_eq_mul, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => by ring

lemma dot_tl {I : Finset ι} {t : ι} (ht : t ∈ I) (u : S t → F) (P : Om S (I.erase t) → F)
    (Z : Om S I → F) : tl ht u P ⬝ᵥ Z = P ⬝ᵥ contr ht u Z := by
  rw [dotProduct, sum_ext ht]
  simp only [tl, ext_at, res_ext, dotProduct, contr, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring

/-- lines of a tensor lift in a direction other than `t` -/
lemma tl_line_ne {I : Finset ι} {t : ι} (ht : t ∈ I) (u : S t → F) (P : Om S (I.erase t) → F)
    (j : {i // i ∈ I.erase t}) (Cj : Submodule F (S j.val → F))
    (hP : ∀ b', (fun s => P (Function.update b' j s)) ∈ Cj) (b : Om S I) :
    (fun s => tl ht u P (Function.update b ⟨j.val, Finset.mem_of_mem_erase j.2⟩ s)) ∈ Cj := by
  have : (fun s => tl ht u P (Function.update b ⟨j.val, Finset.mem_of_mem_erase j.2⟩ s)) =
      u (b (tpt ht)) • (fun s => P (Function.update (res ht b) j s)) := by
    funext s
    simp only [tl, Pi.smul_apply, smul_eq_mul]
    rw [update_ne_at, res_update_ne]
  rw [this]
  exact Cj.smul_mem _ (hP _)

/-- lines of a tensor lift in direction `t` -/
lemma tl_line_t {I : Finset ι} {t : ι} (ht : t ∈ I) (u : S t → F) (P : Om S (I.erase t) → F)
    (Ct : Submodule F (S t → F)) (hu : u ∈ Ct) (b : Om S I) :
    (fun s => tl ht u P (Function.update b (tpt ht) s)) ∈ Ct := by
  have : (fun s => tl ht u P (Function.update b (tpt ht) s)) = P (res ht b) • u := by
    funext s
    simp only [tl, Pi.smul_apply, smul_eq_mul]
    rw [update_t_at, res_update_t, mul_comm]
  rw [this]
  exact Ct.smul_mem _ hu

end PrivPCP.L46Aux


namespace PrivPCP.L46Aux

open GoodQLTC Classical PrivPCP.TDual

variable {F : Type} [Field F]

section generic
variable {κ : Type} [Fintype κ] [DecidableEq κ] {T : κ → Type} [∀ i, Fintype (T i)]

lemma axisCode_congr (C C' : ∀ i, Submodule F (T i → F)) (j : κ) (h : C j = C' j) :
    axisCode C j = axisCode C' j := by
  ext x; rw [mem_axisCode_iff, mem_axisCode_iff, h]

lemma axisCode_mono (C C' : ∀ i, Submodule F (T i → F)) (j : κ) (h : C j ≤ C' j) :
    axisCode C j ≤ axisCode C' j := by
  intro x hx; rw [mem_axisCode_iff] at hx ⊢; exact fun b => h (hx b)

lemma tensorCode_mono (C C' : ∀ i, Submodule F (T i → F)) (h : ∀ j, C j ≤ C' j) :
    tensorCode C ≤ tensorCode C' := iInf_mono fun j => axisCode_mono C C' j (h j)

variable (Y : NestedCodes F κ T)

lemma Kbig_le_C (hKV : ∀ i, Y.K i ≤ Y.V i) : Y.Kbig ≤ Y.C := by
  apply iSup_le
  intro i
  apply tensorCode_mono
  intro j
  by_cases h : j = i
  · subst h; rw [Function.update_self]; exact hKV j
  · rw [Function.update_of_ne h]

lemma B_le_Dbig (hKV : ∀ i, Y.K i ≤ Y.V i) : Y.B ≤ Y.Dbig :=
  dualCode_antitone (Kbig_le_C Y hKV)

lemma B_eq : Y.B = ⨆ j, axisCode Y.U j := dualCode_tensorCode Y.V

lemma Dbig_le_dualE (i : κ) : Y.Dbig ≤ dualCode (Y.E i) :=
  dualCode_antitone (le_iSup Y.E i)

lemma dualE_eq (i : κ) :
    dualCode (Y.E i) = ⨆ j, axisCode (fun j => dualCode (Function.update Y.V i (Y.K i) j)) j :=
  dualCode_tensorCode _

end generic

end PrivPCP.L46Aux


namespace PrivPCP.L46Aux

open GoodQLTC Classical PrivPCP.TDual

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]

lemma functional_eq_dot' {Ω : Type} [Fintype Ω] (ℓ : (Ω → F) →ₗ[F] F) (v : Ω → F) :
    ℓ v = (fun x => ℓ (Pi.single x 1)) ⬝ᵥ v := by
  conv_lhs => rw [pi_eq_sum_univ v]
  rw [map_sum, dotProduct]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  congr 2
  funext y
  simp [Pi.single_apply, eq_comm]

lemma tl_zero {I : Finset ι} {t : ι} (ht : t ∈ I) (u : S t → F) :
    tl ht u (0 : Om S (I.erase t) → F) = 0 := by funext ω; simp [tl]

lemma tl_add {I : Finset ι} {t : ι} (ht : t ∈ I) (u : S t → F) (P P' : Om S (I.erase t) → F) :
    tl ht u (P + P') = tl ht u P + tl ht u P' := by funext ω; simp [tl, mul_add]

variable (X : NestedCodes F ι S)

lemma tl_mem_B {I : Finset ι} {t : ι} (ht : t ∈ I) (u : S t → F) (P : Om S (I.erase t) → F)
    (hP : P ∈ (X.restrict (I.erase t)).B) : tl ht u P ∈ (X.restrict I).B := by
  rw [B_eq] at hP ⊢
  refine Submodule.iSup_induction _ (motive := fun P => tl ht u P ∈ _) hP ?_ ?_ ?_
  · intro j P hPj
    apply Submodule.mem_iSup_of_mem (⟨j.val, Finset.mem_of_mem_erase j.2⟩ : {i // i ∈ I})
    rw [mem_axisCode_iff]
    intro b
    exact tl_line_ne ht u P j _ ((mem_axisCode_iff _ _ _).1 hPj) b
  · rw [tl_zero]; exact Submodule.zero_mem _
  · intro P P' h1 h2; rw [tl_add]; exact Submodule.add_mem _ h1 h2

lemma code_eq {I : Finset ι} {t : ι} (j m : {i // i ∈ I.erase t}) :
    (Function.update (X.restrict I).V ⟨j.val, Finset.mem_of_mem_erase j.2⟩
        ((X.restrict I).K ⟨j.val, Finset.mem_of_mem_erase j.2⟩))
      ⟨m.val, Finset.mem_of_mem_erase m.2⟩ =
    (Function.update (X.restrict (I.erase t)).V j ((X.restrict (I.erase t)).K j)) m := by
  by_cases h : m = j
  · subst h; simp [Function.update_self]; rfl
  · have h' : (⟨m.val, Finset.mem_of_mem_erase m.2⟩ : {i // i ∈ I}) ≠
        ⟨j.val, Finset.mem_of_mem_erase j.2⟩ := by
      intro e; apply h; apply Subtype.ext; have := congrArg Subtype.val e; simpa using this
    rw [Function.update_of_ne h', Function.update_of_ne h]; rfl

lemma tl_mem_Kbig {I : Finset ι} {t : ι} (ht : t ∈ I) (v : S t → F) (hv : v ∈ X.V t)
    (R : Om S (I.erase t) → F) (hR : R ∈ (X.restrict (I.erase t)).Kbig) :
    tl ht v R ∈ (X.restrict I).Kbig := by
  refine Submodule.iSup_induction _ (motive := fun P => tl ht v P ∈ _) hR ?_ ?_ ?_
  · intro j P hPj
    apply Submodule.mem_iSup_of_mem (⟨j.val, Finset.mem_of_mem_erase j.2⟩ : {i // i ∈ I})
    unfold NestedCodes.E tensorCode at hPj ⊢
    rw [Submodule.mem_iInf] at hPj ⊢
    intro m
    rw [mem_axisCode_iff]
    intro b
    by_cases hm : m = tpt ht
    · subst hm
      have hne : (tpt ht : {i // i ∈ I}) ≠ ⟨j.val, Finset.mem_of_mem_erase j.2⟩ := by
        intro e; exact Finset.ne_of_mem_erase j.2 (congrArg Subtype.val e).symm
      rw [Function.update_of_ne hne]
      exact tl_line_t ht v P (X.V t) hv b
    · have hmt : m.val ≠ t := fun e => hm (Subtype.ext e)
      let mJ : {i // i ∈ I.erase t} := ⟨m.val, Finset.mem_erase.2 ⟨hmt, m.2⟩⟩
      have hl := (mem_axisCode_iff _ _ _).1 (hPj mJ)
      have := tl_line_ne ht v P mJ _ hl b
      rw [← code_eq X j mJ] at this
      exact this
  · rw [tl_zero]; exact Submodule.zero_mem _
  · intro P P' h1 h2; rw [tl_add]; exact Submodule.add_mem _ h1 h2

end PrivPCP.L46Aux


namespace PrivPCP.L46Aux

open GoodQLTC Classical PrivPCP.TDual

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]
variable (X : NestedCodes F ι S)

theorem step (hKV : ∀ i, X.K i ≤ X.V i) (I : Finset ι) (t : ι) (ht : t ∈ I)
    (ρ c : ℝ) (hρ : 0 ≤ ρ)
    (hPE : IsProductExpanding ρ ((X.restrict I).mixed fun i => decide (i.val ≠ t)))
    (IH : ∀ M' ∈ (X.restrict (I.erase t)).Dbig, M' ∉ (X.restrict (I.erase t)).B →
      c ≤ supportCard M') :
    ∀ M ∈ (X.restrict I).Dbig, M ∉ (X.restrict I).B →
      ρ * Fintype.card (S t) * c ≤ supportCard M := by
  intro M hM hMB
  have hKVI : ∀ i, (X.restrict I).K i ≤ (X.restrict I).V i := fun i => hKV i.val
  have hfam : (fun j => dualCode (Function.update (X.restrict I).V (tpt ht)
      ((X.restrict I).K (tpt ht)) j)) = (X.restrict I).mixed (fun i => decide (i.val ≠ t)) := by
    funext j
    by_cases h : j = tpt ht
    · subst h
      simp only [Function.update_self, NestedCodes.mixed, ne_eq, not_true_eq_false,
        decide_false]
      rfl
    · have : j.val ≠ t := fun h' => h (Subtype.ext h')
      rw [Function.update_of_ne h]
      simp only [NestedCodes.mixed, ne_eq, this, not_false_eq_true, decide_true, if_true]
      rfl
  have hMa : M ∈ ⨆ j, axisCode ((X.restrict I).mixed fun i => decide (i.val ≠ t)) j := by
    have := Dbig_le_dualE (X.restrict I) (tpt ht) hM
    rw [dualE_eq, hfam] at this; exact this
  obtain ⟨y, hy, hMy, hbound⟩ := hPE.2 M hMa
  set Mt := y (tpt ht) with hMtdef
  have hyB : ∀ j, j ≠ tpt ht → y j ∈ (X.restrict I).B := by
    intro j hj
    rw [B_eq]
    apply Submodule.mem_iSup_of_mem j
    have hjt : j.val ≠ t := fun h' => hj (Subtype.ext h')
    rw [axisCode_congr (X.restrict I).U ((X.restrict I).mixed fun i => decide (i.val ≠ t)) j
      (by simp [NestedCodes.mixed, hjt])]
    exact hy j
  have hrest : M - Mt ∈ (X.restrict I).B := by
    rw [hMy, ← Finset.add_sum_erase _ _ (Finset.mem_univ (tpt ht)), add_sub_cancel_left]
    exact Submodule.sum_mem _ fun j hj => hyB j (Finset.ne_of_mem_erase hj)
  have hMtD : Mt ∈ (X.restrict I).Dbig := by
    have : Mt = M - (M - Mt) := by abel
    rw [this]; exact Submodule.sub_mem _ hM (B_le_Dbig _ hKVI hrest)
  have hMtB : Mt ∉ (X.restrict I).B := by
    intro h; apply hMB
    have : M = (M - Mt) + Mt := by abel
    rw [this]; exact Submodule.add_mem _ hrest h
  -- a contraction that is not in `B`
  have hex : ∃ v ∈ X.V t, contr ht v Mt ∉ (X.restrict (I.erase t)).B := by
    by_contra hcon
    push Not at hcon
    apply hMtB
    let bV := Module.finBasis F (X.V t)
    have hext : ∀ m, ∃ g : (S t → F) →ₗ[F] F, g.comp (X.V t).subtype = bV.coord m :=
      fun m => LinearMap.exists_extend (bV.coord m)
    choose g hg using hext
    let u : Fin (Module.finrank F (X.V t)) → S t → F := fun m s => g m (Pi.single s 1)
    have hu : ∀ m (w : X.V t), u m ⬝ᵥ (w : S t → F) = bV.coord m w := by
      intro m w
      rw [← hg m]
      exact (functional_eq_dot' (g m) w).symm
    set N := Mt - ∑ m, tl ht (u m) (contr ht (bV m) Mt) with hNdef
    have hN : N ∈ (X.restrict I).B := by
      rw [B_eq]
      apply Submodule.mem_iSup_of_mem (tpt ht)
      rw [mem_axisCode_iff]
      intro b v hv
      rw [line_dot_contr]
      have hv' : v = ∑ m, (bV.coord m ⟨v, hv⟩) • (bV m : S t → F) := by
        have h1 := bV.sum_repr ⟨v, hv⟩
        have h2 := congrArg Subtype.val h1
        rw [Submodule.coe_sum] at h2
        simp only [SetLike.val_smul] at h2
        conv_lhs => rw [← h2]
        rfl
      rw [hNdef, contr_sub, contr_fsum]
      simp only [contr_tl]
      have : contr ht v Mt = ∑ m, (bV.coord m ⟨v, hv⟩) • contr ht (bV m) Mt := by
        conv_lhs => rw [hv']
        exact contr_sum ht _ _ Mt
      rw [this]
      have h2 : ∀ m, (v ⬝ᵥ u m) = bV.coord m ⟨v, hv⟩ := by
        intro m; rw [dotProduct_comm]; exact hu m ⟨v, hv⟩
      simp only [h2, sub_self, Pi.zero_apply]
    have hsum : ∑ m, tl ht (u m) (contr ht (bV m) Mt) ∈ (X.restrict I).B :=
      Submodule.sum_mem _ fun m _ => tl_mem_B X ht (u m) _ (hcon _ (bV m).2)
    have : Mt = N + ∑ m, tl ht (u m) (contr ht (bV m) Mt) := by rw [hNdef]; abel
    rw [this]; exact Submodule.add_mem _ hN hsum
  obtain ⟨v, hv, hvB⟩ := hex
  -- the contraction lies in `D` of the smaller tuple
  have hcD : contr ht v Mt ∈ (X.restrict (I.erase t)).Dbig := by
    intro R hR
    rw [← dot_tl]
    exact hMtD _ (tl_mem_Kbig X ht v hv R hR)
  have hc := IH _ hcD hvB
  -- weight of the contraction
  have hwt : supportCard (contr ht v Mt) ≤ lineCount (tpt ht) Mt := by
    unfold supportCard lineCount
    let f : Om S (I.erase t) → ((j : {j : {i // i ∈ I} // j ≠ tpt ht}) → S j.1.val) :=
      fun y j => y ⟨j.1.val, Finset.mem_erase.2 ⟨fun h => j.2 (Subtype.ext h), j.1.2⟩⟩
    apply Finset.card_le_card_of_injOn f
    · intro y hy
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy
      obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
      have hx' : Mt (ext ht x y) ≠ 0 := right_ne_zero_of_mul hx
      simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_image,
        Set.mem_setOf_eq]
      refine ⟨ext ht x y, hx', ?_⟩
      funext j
      exact ext_ne ht x y j.1 (fun h => j.2 (Subtype.ext h))
    · intro y _ y' _ hyy
      funext jJ
      have := congrFun hyy ⟨⟨jJ.val, Finset.mem_of_mem_erase jJ.2⟩,
        fun h => Finset.ne_of_mem_erase jJ.2 (congrArg Subtype.val h)⟩
      simpa [f] using this
  have hle : (Fintype.card (S t) : ℝ) * (lineCount (tpt ht) Mt : ℝ) ≤
      ∑ j, (Fintype.card (S j.val) : ℝ) * (lineCount j (y j) : ℝ) :=
    Finset.single_le_sum (f := fun j => (Fintype.card (S j.val) : ℝ) * (lineCount j (y j) : ℝ))
      (fun j _ => by positivity) (Finset.mem_univ (tpt ht))
  have hs : (0 : ℝ) ≤ ρ * Fintype.card (S t) := by positivity
  calc ρ * Fintype.card (S t) * c
      ≤ ρ * Fintype.card (S t) * (supportCard (contr ht v Mt) : ℝ) :=
        mul_le_mul_of_nonneg_left hc hs
    _ ≤ ρ * Fintype.card (S t) * (lineCount (tpt ht) Mt : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hwt) hs
    _ = ρ * ((Fintype.card (S t) : ℝ) * (lineCount (tpt ht) Mt : ℝ)) := by ring
    _ ≤ ρ * ∑ j, (Fintype.card (S j.val) : ℝ) * (lineCount j (y j) : ℝ) :=
        mul_le_mul_of_nonneg_left hle hρ
    _ ≤ supportCard M := hbound

end PrivPCP.L46Aux


namespace PrivPCP.L46Aux

open GoodQLTC Classical PrivPCP.TDual

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]
variable (X : NestedCodes F ι S)

theorem base (I : Finset ι) (t : ι) (ht : t ∈ I) (hI : I.erase t = ∅) :
    ∀ M ∈ (X.restrict I).Dbig, M ∉ (X.restrict I).B →
      ((sInf {d | ∃ w ∈ X.W t, w ∉ X.U t ∧ supportCard w = d} : ℕ) : ℝ) ≤ supportCard M := by
  intro M hM hMB
  have hall : ∀ j : {i // i ∈ I}, j = tpt ht := by
    intro j
    apply Subtype.ext
    by_contra h
    have : j.val ∈ I.erase t := Finset.mem_erase.2 ⟨h, j.2⟩
    rw [hI] at this; simp at this
  have hMa := Dbig_le_dualE (X.restrict I) (tpt ht) hM
  rw [dualE_eq] at hMa
  have hle : (⨆ j, axisCode (fun j => dualCode (Function.update (X.restrict I).V (tpt ht)
      ((X.restrict I).K (tpt ht)) j)) j) ≤ axisCode (fun j => dualCode (Function.update
      (X.restrict I).V (tpt ht) ((X.restrict I).K (tpt ht)) j)) (tpt ht) := by
    apply iSup_le; intro j; rw [hall j]
  have hMW := hle hMa
  rw [mem_axisCode_iff] at hMW
  simp only [Function.update_self] at hMW
  have hMU : M ∉ axisCode (X.restrict I).U (tpt ht) := by
    intro h; apply hMB; rw [B_eq]; exact Submodule.mem_iSup_of_mem (tpt ht) h
  rw [mem_axisCode_iff] at hMU
  push Not at hMU
  obtain ⟨b, hb⟩ := hMU
  have h1 : sInf {d | ∃ w ∈ X.W t, w ∉ X.U t ∧ supportCard w = d} ≤
      supportCard (fun s => M (Function.update b (tpt ht) s)) :=
    Nat.sInf_le ⟨_, hMW b, hb, rfl⟩
  have h2 : supportCard (fun s => M (Function.update b (tpt ht) s)) ≤ supportCard M := by
    unfold supportCard
    apply Finset.card_le_card_of_injOn (fun s => Function.update b (tpt ht) s)
    · intro s hs
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hs ⊢
      exact hs
    · intro s _ s' _ h
      have := congrFun h (tpt ht)
      simpa using this
  exact_mod_cast h1.trans h2

/-! transport from `restrict I` with `I` containing everything -/

section transport
variable (I : Finset ι) (hI : ∀ i, i ∈ I)

def Tm (ω : ∀ i, S i) : Om S I := fun i => ω i.val
def Ti (ω : Om S I) : ∀ i, S i := fun i => ω ⟨i, hI i⟩

lemma Tm_Ti (ω : Om S I) : Tm I (Ti I hI ω) = ω := by funext i; rfl
lemma Ti_Tm (ω : ∀ i, S i) : Ti I hI (Tm I ω) = ω := by funext i; rfl

lemma Tm_update (b : ∀ i, S i) (j : ι) (s : S j) :
    Tm I (Function.update b j s) = Function.update (Tm I b) ⟨j, hI j⟩ s := by
  funext i
  by_cases h : i.val = j
  · have hi : i = ⟨j, hI j⟩ := Subtype.ext h
    subst hi
    simp [Tm]
  · have hne : i ≠ ⟨j, hI j⟩ := fun e => h (congrArg Subtype.val e)
    rw [Function.update_of_ne hne]
    simp only [Tm]; rw [Function.update_of_ne h]

lemma Ti_update (b : Om S I) (j : {i // i ∈ I}) (s : S j.val) :
    Ti I hI (Function.update b j s) = Function.update (Ti I hI b) j.val s := by
  funext i
  by_cases h : i = j.val
  · subst h; simp [Ti]
  · have hne : (⟨i, hI i⟩ : {i // i ∈ I}) ≠ j := fun e => h (congrArg Subtype.val e)
    rw [Function.update_of_ne h]
    simp only [Ti]; rw [Function.update_of_ne hne]

def TEquiv : (∀ i, S i) ≃ Om S I where
  toFun := Tm I
  invFun := Ti I hI
  left_inv := Ti_Tm I hI
  right_inv := Tm_Ti I hI

lemma dot_T (x : Om S I → F) (y : (∀ i, S i) → F) :
    (fun ω => x (Tm I ω)) ⬝ᵥ y = x ⬝ᵥ (fun ω => y (Ti I hI ω)) := by
  unfold dotProduct
  exact Fintype.sum_equiv (TEquiv I hI) _ _ (fun ω => by simp [TEquiv, Ti_Tm])

include hI in
lemma axis_pull (C : ∀ i, Submodule F (S i → F)) (j : {i // i ∈ I}) (x : Om S I → F)
    (hx : x ∈ axisCode (fun i : {i // i ∈ I} => C i.val) j) :
    (fun ω => x (Tm I ω)) ∈ axisCode C j.val := by
  rw [mem_axisCode_iff] at hx ⊢
  intro b
  have := hx (Tm I b)
  convert this using 2 with s
  rw [Tm_update I hI]

lemma axis_push (C : ∀ i, Submodule F (S i → F)) (j : ι) (x : (∀ i, S i) → F)
    (hx : x ∈ axisCode C j) :
    (fun ω => x (Ti I hI ω)) ∈ axisCode (fun i : {i // i ∈ I} => C i.val) ⟨j, hI j⟩ := by
  rw [mem_axisCode_iff] at hx ⊢
  intro b
  have := hx (Ti I hI b)
  convert this using 2 with s
  rw [Ti_update I hI]

end transport

end PrivPCP.L46Aux


namespace PrivPCP.L46Aux

open GoodQLTC Classical PrivPCP.TDual

variable {F : Type} [Field F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [∀ i, Fintype (S i)]
variable (X : NestedCodes F ι S)

lemma Kbig_pull (I : Finset ι) (hI : ∀ i, i ∈ I) (x : Om S I → F)
    (hx : x ∈ (X.restrict I).Kbig) : (fun ω => x (Tm I ω)) ∈ X.Kbig := by
  refine Submodule.iSup_induction _ (motive := fun x => (fun ω => x (Tm I ω)) ∈ X.Kbig) hx ?_ ?_ ?_
  · intro j x hxj
    apply Submodule.mem_iSup_of_mem j.val
    unfold NestedCodes.E tensorCode at hxj ⊢
    rw [Submodule.mem_iInf] at hxj ⊢
    intro m
    have hfam : Function.update (X.restrict I).V j ((X.restrict I).K j) =
        fun i : {i // i ∈ I} => Function.update X.V j.val (X.K j.val) i.val := by
      funext i
      by_cases h : i = j
      · subst h; simp; rfl
      · have h' : i.val ≠ j.val := fun e => h (Subtype.ext e)
        rw [Function.update_of_ne h, Function.update_of_ne h']; rfl
    have := hxj ⟨m, hI m⟩
    rw [hfam] at this
    exact axis_pull I hI _ ⟨m, hI m⟩ x this
  · simp only [Pi.zero_apply]; exact Submodule.zero_mem _
  · intro x y hx hy
    have : (fun ω => (x + y) (Tm I ω)) = (fun ω => x (Tm I ω)) + (fun ω => y (Tm I ω)) := rfl
    rw [this]; exact Submodule.add_mem _ hx hy

lemma C_push (I : Finset ι) (hI : ∀ i, i ∈ I) (c : (∀ i, S i) → F) (hc : c ∈ X.C) :
    (fun ω => c (Ti I hI ω)) ∈ (X.restrict I).C := by
  unfold NestedCodes.C tensorCode at hc ⊢
  rw [Submodule.mem_iInf] at hc ⊢
  intro m
  exact axis_push I hI X.V m.val c (hc m.val)

theorem transport (I : Finset ι) (hI : ∀ i, i ∈ I) (c : ℝ)
    (h : ∀ M ∈ (X.restrict I).Dbig, M ∉ (X.restrict I).B → c ≤ supportCard M) :
    ∀ M ∈ X.Dbig, M ∉ X.B → c ≤ supportCard M := by
  intro M hM hMB
  set M' : Om S I → F := fun ω => M (Ti I hI ω)
  have hM' : M' ∈ (X.restrict I).Dbig := by
    intro x hx
    rw [← dot_T I hI]
    exact hM _ (Kbig_pull X I hI x hx)
  have hMB' : M' ∉ (X.restrict I).B := by
    intro h'; apply hMB
    intro cc hcc
    have := h' _ (C_push X I hI cc hcc)
    rw [← dot_T I hI] at this
    simpa [Ti_Tm] using this
  have hwt : supportCard M' = supportCard M := by
    unfold supportCard
    refine Finset.card_nbij' (Ti I hI) (Tm I) ?_ ?_ ?_ ?_
    · intro ω hω; simpa using hω
    · intro ω hω; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hω ⊢
      simpa [M', Ti_Tm] using hω
    · intro ω _; exact Tm_Ti I hI ω
    · intro ω _; exact Ti_Tm I hI ω
  rw [← hwt]
  exact h M' hM' hMB'

end PrivPCP.L46Aux

open PrivPCP PrivPCP.L46Aux GoodQLTC Classical

theorem solution {F : Type} [Field F] [Fintype F] {k : ℕ} (hk : 2 ≤ k) {S : Fin k → Type}
    [∀ i, Fintype (S i)] (X : NestedCodes F (Fin k) S) (hX : X.Valid) (ρ : ℝ)
    (hPE : ∀ t : Fin k, t.val + 1 < k →
      GoodQLTC.IsProductExpanding ρ
        ((X.restrict (Finset.univ.filter fun i => t ≤ i)).mixed fun i => decide (i.val ≠ t))) :
    ∀ M ∈ X.Dbig, M ∉ X.B →
      (⨅ i, X.relDualDist i) * ρ ^ (k - 1) * (Fintype.card (∀ i, S i) : ℝ) ≤ GoodQLTC.supportCard M := by
  have hKV : ∀ i, X.K i ≤ X.V i := fun i => (hX i).2.le
  have hρ : 0 ≤ ρ := (hPE ⟨0, by omega⟩ (by simp; omega)).1.le
  set δ := ⨅ i, X.relDualDist i
  let Iset : Fin k → Finset (Fin k) := fun t => Finset.univ.filter fun i => t ≤ i
  have hmem : ∀ t : Fin k, t ∈ Iset t := fun t => by simp [Iset]
  -- the chain
  have chain : ∀ n : ℕ, ∀ t : Fin k, t.val + n = k - 1 →
      ∀ M ∈ (X.restrict (Iset t)).Dbig, M ∉ (X.restrict (Iset t)).B →
        δ * ρ ^ n * ∏ i ∈ Iset t, (Fintype.card (S i) : ℝ) ≤ supportCard M := by
    intro n
    induction n with
    | zero =>
      intro t ht M hM hMB
      have herase : (Iset t).erase t = ∅ := by
        ext i
        simp only [Iset, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false, not_and]
        intro hne hle
        have : t.val < i.val := lt_of_le_of_ne hle (fun e => hne (Fin.ext e).symm)
        have := i.isLt
        omega
      have hb := base X (Iset t) t (hmem t) herase M hM hMB
      have hsingle : Iset t = {t} := by
        rw [← Finset.insert_erase (hmem t), herase]; rfl
      have hp : ∏ i ∈ Iset t, (Fintype.card (S i) : ℝ) = Fintype.card (S t) := by
        rw [hsingle, Finset.prod_singleton]
      rw [hp, pow_zero, mul_one]
      have hδ : δ ≤ X.relDualDist t := ciInf_le (Set.finite_range _).bddBelow t
      have hs : (0 : ℝ) ≤ Fintype.card (S t) := by positivity
      calc δ * (Fintype.card (S t) : ℝ) ≤ X.relDualDist t * Fintype.card (S t) :=
            mul_le_mul_of_nonneg_right hδ hs
        _ ≤ supportCard M := by
            unfold NestedCodes.relDualDist
            rcases eq_or_lt_of_le hs with h0 | hpos
            · rw [← h0, mul_zero]; positivity
            · rw [div_mul_cancel₀ _ hpos.ne']; exact hb
    | succ n ih =>
      intro t ht M hM hMB
      have ht1 : t.val + 1 < k := by omega
      set t' : Fin k := ⟨t.val + 1, ht1⟩
      have herase : (Iset t).erase t = Iset t' := by
        ext i
        simp only [Iset, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, t']
        constructor
        · rintro ⟨hne, hle⟩
          have : t.val < i.val := lt_of_le_of_ne hle (fun e => hne (Fin.ext e).symm)
          show t.val + 1 ≤ i.val; omega
        · intro h
          have h' : t.val + 1 ≤ i.val := h
          refine ⟨fun e => ?_, ?_⟩
          · rw [e] at h'; omega
          · show t.val ≤ i.val; omega
      have IH := ih t' (by simp [t']; omega)
      rw [← herase] at IH
      have hstep := step X hKV (Iset t) t (hmem t) ρ _ hρ (hPE t ht1) IH M hM hMB
      have hp : ∏ i ∈ Iset t, (Fintype.card (S i) : ℝ) =
          Fintype.card (S t) * ∏ i ∈ Iset t', (Fintype.card (S i) : ℝ) := by
        rw [← Finset.mul_prod_erase _ _ (hmem t), herase]
      rw [hp]
      calc δ * ρ ^ (n + 1) * ((Fintype.card (S t) : ℝ) * ∏ i ∈ Iset t', (Fintype.card (S i) : ℝ))
          = ρ * Fintype.card (S t) * (δ * ρ ^ n * ∏ i ∈ Iset t', (Fintype.card (S i) : ℝ)) := by
            ring
        _ ≤ supportCard M := by rw [← herase]; exact hstep
  have h0 := chain (k - 1) ⟨0, by omega⟩ (by simp) 
  have hall : ∀ i, i ∈ Iset ⟨0, by omega⟩ := fun i => by
    simp only [Iset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Fin.mk_le_of_le_val (Nat.zero_le _)
  have := transport X (Iset ⟨0, by omega⟩) hall _ h0
  intro M hM hMB
  have hcard : (Fintype.card (∀ i, S i) : ℝ) = ∏ i ∈ Iset ⟨0, by omega⟩, (Fintype.card (S i) : ℝ) := by
    rw [Fintype.card_pi]
    push_cast
    rw [Finset.eq_univ_of_forall hall]
  rw [hcard]
  exact this M hM hMB


