-- Prove2me | solution 1 for RightRepair.Equilibrium.table_G1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T08:06:27.36024+00:00
-- url     : https://prove2.me/submissions/4e579b89-fc52-4c8e-bae8-65c0eebdf956

-- Research directed by Alexander Richard Towell (queelius); Lean formalization by OpenAI Codex.
-- Source authors: Chen Jin, Luyi Yang and Cungen Zhu.
-- Platform definitions and formulation: mikedeng1; review: Shuze Chen.
-- Prior G.41 correction belongs to mikedeng1; prior G.51 proof belongs to carlok.
-- Formal foundations: Lean and Mathlib contributors.
import Mathlib
import Definitions.Def_RightRepair_Equilibrium_Setting
set_option autoImplicit false
set_option maxHeartbeats 1200000
open RightRepair.Equilibrium
namespace RepairResearch
lemma full_gap (P : Params) (hP : Standing P) (pn pr : ℝ) :
    profit4 P pn pr = (P.c-P.δ+P.cM*P.f-1)^2/(4*(1+3*P.δ))-
      (pn+P.f*pr-(P.c+P.δ+P.cM*P.f+1)/2)^2/(1+3*P.δ) := by
  have hd : 0<1+3*P.δ := by linarith [hP.δ_pos]
  unfold profit4 theta2Problem4
  field_simp [ne_of_gt hd]
  ring_nf
  field_simp [show 1+P.δ*3≠0 by linarith [hP.δ_pos]]
  <;> ring
lemma full_feasible (P : Params) (hP : Standing P) : feasible4 P (pnFull P) 0 := by
  have hf : 0<P.f := hP.f_pos
  have hm : 0≤P.cM*P.f := mul_nonneg hP.cM_nonneg hf.le
  have hd : 0<P.δ := hP.δ_pos
  have hδ : P.δ<1 := hP.δ_lt_one
  have hh : 0<1+P.δ+2*P.δ*(1-P.f) := by have := hP.f_lt_one; positivity
  unfold feasible4 pnFull
  refine ⟨?_,?_,le_rfl,?_,?_,?_⟩
  · linarith [hP.c_nonneg]
  · linarith [hP.c_lt]
  · linarith [hP.cM_nonneg,hP.cM_le_cI]
  · apply div_nonneg _ hf.le; linarith [hP.c_lt]
  · apply div_nonneg _ hh.le
    apply mul_nonneg hd.le
    linarith [hP.c_nonneg]
lemma full_opt (P : Params) (hP : Standing P) :
    let v := (P.c-P.δ+P.cM*P.f-1)^2/(4*(1+3*P.δ))
    let l := (P.c+P.δ+P.cM*P.f+1)/2
    (∀ pn pr,feasible4 P pn pr → profit4 P pn pr≤v) ∧
    (∃ pn pr,feasible4 P pn pr ∧ pn+P.f*pr=l ∧ profit4 P pn pr=v) ∧
    (∀ pn pr,feasible4 P pn pr → pn+P.f*pr=l → profit4 P pn pr=v) := by
  dsimp
  have hd : 0≤1+3*P.δ := by linarith [hP.δ_pos]
  refine ⟨?_,?_,?_⟩
  · intro pn pr _
    rw [full_gap P hP]
    exact sub_le_self _ (div_nonneg (sq_nonneg _) hd)
  · have hl : pnFull P+P.f*0=(P.c+P.δ+P.cM*P.f+1)/2 := by unfold pnFull; ring
    refine ⟨pnFull P,0,full_feasible P hP,hl,?_⟩
    rw [full_gap P hP,hl]
    simp
  · intro pn pr _ he
    rw [full_gap P hP,he]
    simp
lemma partial_quadratic (P : Params) (hP : Standing P) (z u : ℝ) :
    (((1-P.δ)*z+(2-P.f)*u)-P.c)*(1-z)+
      (u-P.cM)*((2-P.f)*z-(1-P.f)-u/P.δ) =
    -(1-P.δ)*z^2+(1-P.δ+P.c-P.cM*(2-P.f))*z+
      (1+P.cM/P.δ)*u-u^2/P.δ-P.c+P.cM*(1-P.f) := by
  field_simp
  ring
lemma partial_gap (P : Params) (hP : Standing P) (z u : ℝ) :
    let zstar := (1-P.δ+P.c-P.cM*(2-P.f))/(2*(1-P.δ))
    let ustar := (P.δ+P.cM)/2
    let F := fun z u : ℝ => -(1-P.δ)*z^2+(1-P.δ+P.c-P.cM*(2-P.f))*z+
      (1+P.cM/P.δ)*u-u^2/P.δ-P.c+P.cM*(1-P.f)
    F zstar ustar-F z u = (1-P.δ)*(z-zstar)^2+(u-ustar)^2/P.δ := by
  dsimp
  have h1 : 0<1-P.δ := sub_pos.mpr hP.δ_lt_one
  have h2 : 0<P.δ := hP.δ_pos
  field_simp
  ring
end RepairResearch
open Set
namespace RepairResearch
lemma boundary_le (f : ℝ → ℝ) (hf : Continuous f) (l r : ℝ) (hlr : l<r)
    (h : ∀ x ∈ Ioo l r, f x≤0) : f r≤0 := by
  have hs : IsClosed {x : ℝ | f x≤0} := isClosed_le hf continuous_const
  have hc := closure_minimal (show Ioo l r ⊆ {x : ℝ | f x≤0} from h) hs
  apply hc
  rw [closure_Ioo (ne_of_lt hlr)]
  exact ⟨hlr.le,le_rfl⟩
lemma positive_market (P : Params) (hP : Standing P) (pn : ℝ) (pr : Option ℝ)
    (pu α θ₁ θ₂ : ℝ) (h : MarketEq P pn pr pu α θ₁ θ₂)
    (hpu : 0<pu) (ht : θ₂<1) :
    θ₁=pu/P.δ ∧
    θ₂-θ₁=(1-θ₂)*(1-P.f+P.f*α) ∧
    pn=(1-P.δ)*θ₂+(2-P.f)*pu+P.f*max (pu-effRepair P pr) 0 := by
  rcases h with ⟨_,ha0,ha1,h10,h12,h21,hseg,hr1,hr0,hclear⟩
  have hclear' : θ₂-θ₁=(1-θ₂)*(1-P.f+P.f*α) := by
    rcases hclear with h | ⟨hz,_⟩
    · exact h
    · linarith
  have hh : 0<1-P.f+P.f*α := by nlinarith [hP.f_lt_one,mul_nonneg hP.f_pos.le ha0]
  have h12' : θ₁<θ₂ := by have := mul_pos (sub_pos.mpr ht) hh; linarith
  have hs : ∀ θ : ℝ,0≤θ → θ≤1 →
      (θ<θ₁ → uNew P pn pr pu θ≤0 ∧ uUsed P pu θ≤0) ∧
      (θ₁≤θ → θ<θ₂ → 0≤uUsed P pu θ ∧ uNew P pn pr pu θ≤uUsed P pu θ) ∧
      (θ₂≤θ → 0≤uNew P pn pr pu θ ∧ uUsed P pu θ≤uNew P pn pr pu θ) := by
    rcases hseg with ⟨_,he,_⟩ | hs
    · linarith
    · exact hs
  have hu0 : 0≤uUsed P pu θ₁ := (hs θ₁ h10 (h12.trans h21)).2.1 le_rfl h12' |>.1
  have h1p : 0<θ₁ := by
    unfold uUsed at hu0
    by_contra hn
    have hz : θ₁=0 := by linarith
    rw [hz] at hu0
    linarith
  have hu1 : uUsed P pu θ₁≤0 := by
    apply boundary_le (uUsed P pu) (by unfold uUsed; fun_prop) 0 θ₁ h1p
    intro x hx
    exact (hs x hx.1.le (hx.2.le.trans (h12.trans h21))).1 hx.2 |>.2
  have he1 : θ₁=pu/P.δ := by apply (eq_div_iff (ne_of_gt hP.δ_pos)).mpr; unfold uUsed at hu0 hu1; nlinarith
  have hd0 : uNew P pn pr pu θ₂-uUsed P pu θ₂≤0 := by
    apply boundary_le (fun x => uNew P pn pr pu x-uUsed P pu x)
      (by unfold uNew uUsed; fun_prop) θ₁ θ₂ h12'
    intro x hx
    have hh := (hs x (h10.trans hx.1.le) (hx.2.le.trans h21)).2.1 hx.1.le hx.2
    linarith [hh.2]
  have hd1 : uUsed P pu θ₂≤uNew P pn pr pu θ₂ := (hs θ₂ (h10.trans h12) h21).2.2 le_rfl |>.2
  refine ⟨he1,hclear',?_⟩
  unfold uNew uUsed at hd0 hd1
  linarith
lemma positive_partial_bounds (P : Params) (hP : Standing P) (pn : ℝ) (pr : Option ℝ)
    (pu α θ₁ θ₂ : ℝ) (h : MarketEq P pn pr pu α θ₁ θ₂)
    (hpu : 0<pu) (ht : θ₂<1) (he : pu≤effRepair P pr) :
    pu≤P.cI ∧ P.δ*(2*θ₂-1)≤pu ∧ pu≤P.δ*((2-P.f)*θ₂-(1-P.f)) ∧
    pn=(1-P.δ)*θ₂+(2-P.f)*pu := by
  have hm := positive_market P hP pn pr pu α θ₁ θ₂ h hpu ht
  have hci : effRepair P pr≤P.cI := by cases pr <;> simp [effRepair]
  rcases h with ⟨_,ha0,ha1,h10,h12,h21,hseg,hr1,hr0,hclear⟩
  have hprod : 0≤P.f*α*(1-θ₂) := by have := hP.f_pos; positivity
  have hprod1 : P.f*α*(1-θ₂)≤P.f*(1-θ₂) := by
    have := mul_le_mul_of_nonneg_right ha1 (mul_nonneg hP.f_pos.le (sub_nonneg.mpr h21)); nlinarith
  have heq : P.δ*(θ₂-(1-θ₂)*(1-P.f+P.f*α))=pu := by
    rw [←hm.2.1]; have := (eq_div_iff (ne_of_gt hP.δ_pos)).mp hm.1; nlinarith
  refine ⟨he.trans hci,?_,?_,?_⟩
  · have := mul_le_mul_of_nonneg_left hprod1 hP.δ_pos.le; nlinarith
  · have := mul_nonneg hP.δ_pos.le hprod; nlinarith
  · simpa only [max_eq_right (sub_nonpos.mpr he),mul_zero,add_zero] using hm.2.2
end RepairResearch
namespace RepairResearch
noncomputable def partialF (P : Params) (z u : ℝ) : ℝ :=
  -(1-P.δ)*z^2+(1-P.δ+P.c-P.cM*(2-P.f))*z+
    (1+P.cM/P.δ)*u-u^2/P.δ-P.c+P.cM*(1-P.f)
lemma profit_le_eff (P : Params) (hP : Standing P) (pn : ℝ) (pr : Option ℝ)
    (α z : ℝ) (ha : 0≤α) (hz : z≤1) :
    profit P pn pr α z ≤ (pn-P.c+(effRepair P pr-P.cM)*P.f*α)*(1-z) := by
  have hcoef : 0≤(1-z)*P.f*α := by have := hP.f_pos; positivity
  cases pr with
  | none =>
    simp only [profit,effRepair,add_zero]
    have hp := mul_nonneg (sub_nonneg.mpr hP.cM_le_cI) hcoef
    nlinarith
  | some r =>
    by_cases hr : r≤P.cI
    · simp only [profit,effRepair,if_pos hr,min_eq_right hr]
      ring_nf
      exact le_rfl
    · simp only [profit,effRepair,if_neg hr,min_eq_left (le_of_not_ge hr),add_zero]
      have hp := mul_nonneg (sub_nonneg.mpr hP.cM_le_cI) hcoef
      nlinarith
lemma partial_profit_bound (P : Params) (hP : Standing P) (pn : ℝ) (pr : Option ℝ)
    (pu α θ₁ θ₂ : ℝ) (h : MarketEq P pn pr pu α θ₁ θ₂)
    (hpu : 0<pu) (ht : θ₂<1) (he : pu≤effRepair P pr) :
    profit P pn pr α θ₂≤partialF P θ₂ pu := by
  have hm := positive_market P hP pn pr pu α θ₁ θ₂ h hpu ht
  have hb := positive_partial_bounds P hP pn pr pu α θ₁ θ₂ h hpu ht he
  have ha0 : 0≤α := h.2.1
  have hz : θ₂≤1 := h.2.2.2.2.2.1
  have hqty : P.f*α*(1-θ₂)=(2-P.f)*θ₂-(1-P.f)-pu/P.δ := by
    have hc := hm.2.1
    rw [hm.1] at hc
    nlinarith
  have hα : (effRepair P pr-P.cM)*P.f*α*(1-θ₂)=(pu-P.cM)*P.f*α*(1-θ₂) := by
    by_cases ha : α=0
    · simp [ha]
    · have heq : pu=effRepair P pr := by
        by_contra hn
        have hp : pu<effRepair P pr := lt_of_le_of_ne he hn
        exact ha (h.2.2.2.2.2.2.2.2.1 hp)
      rw [heq]
  calc
    _ ≤ (pn-P.c+(effRepair P pr-P.cM)*P.f*α)*(1-θ₂) := profit_le_eff P hP pn pr α θ₂ ha0 hz
    _ = (pn-P.c)*(1-θ₂)+(pu-P.cM)*(P.f*α*(1-θ₂)) := by nlinarith [hα]
    _ = (((1-P.δ)*θ₂+(2-P.f)*pu)-P.c)*(1-θ₂)+
        (pu-P.cM)*((2-P.f)*θ₂-(1-P.f)-pu/P.δ) := by rw [hqty,hb.2.2.2]
    _ = partialF P θ₂ pu := partial_quadratic P hP θ₂ pu
lemma full_profit_bound (P : Params) (hP : Standing P) (pn : ℝ) (pr : Option ℝ)
    (pu α θ₁ θ₂ : ℝ) (h : MarketEq P pn pr pu α θ₁ θ₂)
    (hpu : 0<pu) (ht : θ₂<1) (he : effRepair P pr<pu) :
    profit P pn pr α θ₂≤(P.c-P.δ+P.cM*P.f-1)^2/(4*(1+3*P.δ)) := by
  have hm := positive_market P hP pn pr pu α θ₁ θ₂ h hpu ht
  have ha : α=1 := h.2.2.2.2.2.2.2.1 he
  have hd : 0<1+3*P.δ := by linarith [hP.δ_pos]
  have hθ : theta2Problem4 P pn (effRepair P pr)=θ₂ := by
    have hclear := hm.2.1
    rw [ha] at hclear
    have h1 := (eq_div_iff (ne_of_gt hP.δ_pos)).mp hm.1
    have hpn := hm.2.2
    rw [max_eq_left (sub_nonneg.mpr he.le)] at hpn
    unfold theta2Problem4
    apply (div_eq_iff (ne_of_gt hd)).mpr
    nlinarith
  have hp := profit_le_eff P hP pn pr α θ₂ h.2.1 h.2.2.2.2.2.1
  rw [ha] at hp ⊢
  have heq : (pn-P.c+(effRepair P pr-P.cM)*P.f*1)*(1-θ₂)=profit4 P pn (effRepair P pr) := by
    unfold profit4
    rw [hθ]; ring
  rw [heq,full_gap P hP] at hp
  have hn : 0≤(pn+P.f*effRepair P pr-(P.c+P.δ+P.cM*P.f+1)/2)^2/(1+3*P.δ) := by positivity
  linarith
end RepairResearch
namespace RepairResearch
lemma eff_nonneg (P : Params) (hP : Standing P) (pr : Option ℝ) (hr : repairAdmissible pr) :
    0≤effRepair P pr := by
  have hi : 0≤P.cI := hP.cM_nonneg.trans hP.cM_le_cI
  cases pr with
  | none => exact hi
  | some r => exact le_min hi (hr r rfl)
lemma zero_market (P : Params) (hP : Standing P) (pn : ℝ) (pr : Option ℝ)
    (α θ₁ θ₂ : ℝ) (h : MarketEq P pn pr 0 α θ₁ θ₂)
    (hpn : 0≤pn) (hr : repairAdmissible pr) (ht : θ₂<1) :
    θ₁=0 ∧ pn=(1-P.δ)*θ₂ ∧
    θ₂≤(1-θ₂)*(1-P.f+P.f*α) ∧ θ₂≤1/2 := by
  rcases h with ⟨_,ha0,ha1,h10,h12,h21,hseg,hr1,hr0,hclear⟩
  have he := eff_nonneg P hP pr hr
  have hs := hseg.resolve_left (by rintro ⟨_,hx,_⟩; linarith)
  have hn : ∀ θ : ℝ, uNew P pn pr 0 θ=θ-pn := by
    intro θ
    simp only [uNew,mul_zero,zero_sub,max_eq_right (neg_nonpos.mpr he),add_zero]
  have hu : ∀ θ : ℝ, uUsed P 0 θ=P.δ*θ := by intro θ; simp [uUsed]
  have h1 : θ₁=0 := by
    by_contra hne
    have hp : 0<θ₁ := lt_of_le_of_ne h10 (Ne.symm hne)
    have hv := (hs (θ₁/2) (by linarith) (by linarith)).1 (by linarith)
    rw [hu] at hv
    nlinarith [mul_pos hP.δ_pos hp]
  have hp0 := (hs θ₂ (h10.trans h12) h21).2.2 le_rfl |>.2
  rw [hn,hu] at hp0
  have hp1 : θ₂-pn-P.δ*θ₂≤0 := by
    by_cases hz : θ₂=0
    · rw [hz]; linarith
    · have hp : 0<θ₂ := by rw [h1] at h12; exact lt_of_le_of_ne h12 (Ne.symm hz)
      apply boundary_le (fun θ : ℝ => θ-pn-P.δ*θ) (by fun_prop) 0 θ₂ hp
      intro x hx
      have hv := (hs x hx.1.le (hx.2.le.trans h21)).2.1 (by rw [h1]; exact hx.1.le) hx.2 |>.2
      rw [hn,hu] at hv
      linarith
  have hc : θ₂≤(1-θ₂)*(1-P.f+P.f*α) := by
    rcases hclear with hc | ⟨_,hc⟩ <;> rw [h1] at hc <;> linarith
  refine ⟨h1,by nlinarith,hc,?_⟩
  have hm := mul_le_mul_of_nonneg_right ha1 (mul_nonneg hP.f_pos.le (sub_nonneg.mpr h21))
  nlinarith
lemma zero_profit_bound (P : Params) (hP : Standing P) (pn : ℝ) (pr : Option ℝ)
    (α θ₁ θ₂ : ℝ) (h : MarketEq P pn pr 0 α θ₁ θ₂)
    (hpn : 0≤pn) (hr : repairAdmissible pr) (ht : θ₂<1) :
    ∃ z : ℝ, 0≤z ∧ z≤1 ∧ P.δ*(2*z-1)≤0 ∧
      0≤P.δ*((2-P.f)*z-(1-P.f)) ∧ profit P pn pr α θ₂≤partialF P z 0 := by
  have hm := zero_market P hP pn pr α θ₁ θ₂ h hpn hr ht
  have he := eff_nonneg P hP pr hr
  have hz0 : 0≤θ₂ := h.2.2.2.1.trans h.2.2.2.2.1
  have ha0 : 0≤α := h.2.1
  have hα : effRepair P pr*α=0 := by
    by_cases he0 : effRepair P pr=0
    · simp [he0]
    · have hp : 0<effRepair P pr := lt_of_le_of_ne he (Ne.symm he0)
      rw [h.2.2.2.2.2.2.2.2.1 hp,mul_zero]
  have hb := profit_le_eff P hP pn pr α θ₂ ha0 ht.le
  have hecoef : effRepair P pr*P.f*α*(1-θ₂)=0 := by
    calc
      _ = (effRepair P pr*α)*(P.f*(1-θ₂)) := by ring
      _ = 0 := by rw [hα]; ring
  have hb' : profit P pn pr α θ₂ ≤ (pn-P.c)*(1-θ₂)-P.cM*P.f*α*(1-θ₂) := by nlinarith [hecoef]
  let z0 := (1-P.f)/(2-P.f)
  have hf : 0<2-P.f := by linarith [hP.f_lt_one]
  have hz00 : 0≤z0 := by dsimp [z0]; exact div_nonneg (sub_nonneg.mpr hP.f_lt_one.le) hf.le
  have hz01 : z0≤1/2 := by dsimp [z0]; apply (div_le_iff₀ hf).mpr; linarith [hP.f_pos]
  have hz0eq : (2-P.f)*z0=1-P.f := by dsimp [z0]; field_simp
  by_cases hz : z0≤θ₂
  · refine ⟨θ₂,hz0,ht.le,?_,?_,?_⟩
    · exact mul_nonpos_of_nonneg_of_nonpos hP.δ_pos.le (by linarith [hm.2.2.2])
    · apply mul_nonneg hP.δ_pos.le
      nlinarith [mul_le_mul_of_nonneg_left hz hf.le]
    · have hc := mul_le_mul_of_nonneg_left hm.2.2.1 hP.cM_nonneg
      rw [hm.2.1] at hb' ⊢
      norm_num [partialF]
      nlinarith
  · refine ⟨z0,hz00,by linarith,?_,?_,?_⟩
    · exact mul_nonpos_of_nonneg_of_nonpos hP.δ_pos.le (by linarith)
    · rw [hz0eq,sub_self,mul_zero]
    · have hn : 0≤P.cM*P.f*α*(1-θ₂) := by have := hP.cM_nonneg; have := hP.f_pos; positivity
      have hmono : ((1-P.δ)*θ₂-P.c)*(1-θ₂) ≤ ((1-P.δ)*z0-P.c)*(1-z0) := by
        have hp : 0≤(z0-θ₂)*((1-P.δ)*(1-z0-θ₂)+P.c) := by
          apply mul_nonneg (by linarith)
          exact add_nonneg (mul_nonneg (sub_nonneg.mpr hP.δ_lt_one.le) (by linarith)) hP.c_nonneg
        nlinarith
      have hv : partialF P z0 0=((1-P.δ)*z0-P.c)*(1-z0) := by
        have hzero : P.cM*((2-P.f)*z0-(1-P.f))=0 := by rw [hz0eq]; ring
        norm_num [partialF]
        nlinarith [hzero]
      rw [hv]
      rw [hm.2.1] at hb' ⊢
      linarith
end RepairResearch
namespace RepairResearch
lemma construct_market (P : Params) (hP : Standing P) (pn : ℝ) (pr : Option ℝ)
    (pu α θ₁ θ₂ : ℝ) (hpu : 0≤pu) (ha0 : 0≤α) (ha1 : α≤1)
    (h10 : 0≤θ₁) (h12 : θ₁≤θ₂) (h21 : θ₂≤1)
    (hu : pu=P.δ*θ₁)
    (hn : pn=(1-P.δ)*θ₂+(2-P.f)*pu+P.f*max (pu-effRepair P pr) 0)
    (hr1 : effRepair P pr<pu → α=1) (hr0 : pu<effRepair P pr → α=0)
    (hc : θ₂-θ₁=(1-θ₂)*(1-P.f+P.f*α)) : MarketEq P pn pr pu α θ₁ θ₂ := by
  refine ⟨hpu,ha0,ha1,h10,h12,h21,Or.inr ?_,hr1,hr0,Or.inl hc⟩
  intro θ hθ0 hθ1
  have heU : uUsed P pu θ=P.δ*(θ-θ₁) := by unfold uUsed; rw [hu]; ring
  have heN : uNew P pn pr pu θ-uUsed P pu θ=(1-P.δ)*(θ-θ₂) := by unfold uNew uUsed; rw [hn]; ring
  have hd : 0≤P.δ := hP.δ_pos.le
  have hd1 : 0≤1-P.δ := sub_nonneg.mpr hP.δ_lt_one.le
  refine ⟨?_,?_,?_⟩
  · intro hθ
    have hp := mul_nonpos_of_nonneg_of_nonpos hd (show θ-θ₁≤0 by linarith)
    have hq := mul_nonpos_of_nonneg_of_nonpos hd1 (show θ-θ₂≤0 by linarith)
    constructor <;> linarith
  · intro hl hh
    have hp := mul_nonneg hd (show 0≤θ-θ₁ by linarith)
    have hq := mul_nonpos_of_nonneg_of_nonpos hd1 (show θ-θ₂≤0 by linarith)
    constructor <;> linarith
  · intro hθ
    have hp := mul_nonneg hd (show 0≤θ-θ₁ by linarith)
    have hq := mul_nonneg hd1 (show 0≤θ-θ₂ by linarith)
    constructor <;> linarith
lemma partial_construct (P : Params) (hP : Standing P) (z u : ℝ)
    (hz0 : 0≤z) (hz1 : z<1) (hu0 : 0≤u) (hui : u≤P.cI)
    (hl : P.δ*(2*z-1)≤u) (hh : u≤P.δ*((2-P.f)*z-(1-P.f))) :
    let α := ((2-P.f)*z-(1-P.f)-u/P.δ)/(P.f*(1-z))
    let pn := (1-P.δ)*z+(2-P.f)*u
    0≤pn ∧ repairAdmissible (some u) ∧
    MarketEq P pn (some u) u α (u/P.δ) z ∧ profit P pn (some u) α z=partialF P z u := by
  dsimp only
  have hd : 0<P.δ := hP.δ_pos
  have hf : 0<P.f := hP.f_pos
  have hd0 : P.δ≠0 := ne_of_gt hd
  have hden : 0<P.f*(1-z) := mul_pos hf (sub_pos.mpr hz1)
  have he : effRepair P (some u)=u := by simp [effRepair,min_eq_right hui]
  have hpn : 0≤(1-P.δ)*z+(2-P.f)*u := by
    have h1 : 0≤1-P.δ := sub_nonneg.mpr hP.δ_lt_one.le
    have h2 : 0≤2-P.f := by linarith [hP.f_lt_one]
    positivity
  have ha0 : 0≤((2-P.f)*z-(1-P.f)-u/P.δ)/(P.f*(1-z)) := by
    apply div_nonneg _ hden.le
    have := (div_le_iff₀ hd).mpr (by nlinarith [hh] : u≤((2-P.f)*z-(1-P.f))*P.δ)
    nlinarith
  have ha1 : ((2-P.f)*z-(1-P.f)-u/P.δ)/(P.f*(1-z))≤1 := by
    apply (div_le_one hden).mpr
    have := (le_div_iff₀ hd).mpr (by nlinarith [hl] : (2*z-1)*P.δ≤u)
    nlinarith
  have h12 : u/P.δ≤z := by
    apply (div_le_iff₀ hd).mpr
    have hp := mul_nonneg (sub_nonneg.mpr hP.f_lt_one.le) (sub_nonneg.mpr hz1.le)
    have hmul := mul_nonneg hd.le hp
    nlinarith
  have hc : z-u/P.δ=(1-z)*(1-P.f+P.f*(((2-P.f)*z-(1-P.f)-u/P.δ)/(P.f*(1-z)))) := by
    field_simp [ne_of_gt hden,ne_of_gt hf,ne_of_gt (sub_pos.mpr hz1),hd0]
    ring
  refine ⟨hpn,?_,?_,?_⟩
  · intro r hr; cases Option.some.inj hr; exact hu0
  · apply construct_market P hP _ _ _ _ _ _ hu0 ha0 ha1 (div_nonneg hu0 hd.le) h12 hz1.le
    · field_simp
    · simp [he]
    · intro h; rw [he] at h; exact (lt_irrefl u h).elim
    · intro h; rw [he] at h; exact (lt_irrefl u h).elim
    · exact hc
  · simp only [profit,if_pos hui]
    have hqty : P.f*(((2-P.f)*z-(1-P.f)-u/P.δ)/(P.f*(1-z)))*(1-z) = (2-P.f)*z-(1-P.f)-u/P.δ := by
      field_simp [ne_of_gt hden,ne_of_gt hf,ne_of_gt (sub_pos.mpr hz1)]
    have hq := congrArg (fun v : ℝ => (u-P.cM)*v) hqty
    have hpartial := partial_quadratic P hP z u
    unfold partialF
    nlinarith
end RepairResearch
namespace RepairResearch
lemma full_construct (P : Params) (hP : Standing P) :
    ∃ θ₁ θ₂, 0≤pnFull P ∧ repairAdmissible (some 0) ∧
      MarketEq P (pnFull P) (some 0) (puFull P) 1 θ₁ θ₂ ∧
      profit P (pnFull P) (some 0) 1 θ₂ = (P.c-P.δ+P.cM*P.f-1)^2/(4*(1+3*P.δ)) := by
  let z := (2*P.δ+pnFull P)/(1+3*P.δ)
  let u := puFull P
  have hd : 0<P.δ := hP.δ_pos
  have hden : 0<1+3*P.δ := by positivity
  have hi : 0≤P.cI := hP.cM_nonneg.trans hP.cM_le_cI
  have hm : 0≤P.cM*P.f := mul_nonneg hP.cM_nonneg hP.f_pos.le
  have hu : 0<u := by
    dsimp [u,puFull]
    apply div_pos _ hden
    apply mul_pos hd
    linarith [hP.c_nonneg]
  have hz1 : z<1 := by
    dsimp [z,pnFull]
    apply (div_lt_one hden).mpr
    linarith [hP.c_lt]
  have hbal : u/P.δ=2*z-1 := by
    dsimp [u,z,puFull,pnFull]
    field_simp [ne_of_gt hd,ne_of_gt hden]
    ring
  have hz0 : 0≤u/P.δ := div_nonneg hu.le hd.le
  have h12 : u/P.δ≤z := by linarith
  have he : effRepair P (some 0)=0 := by simp [effRepair,min_eq_right hi]
  have hpn : 0≤pnFull P := by unfold pnFull; linarith [hP.c_nonneg]
  have hn : pnFull P=(1-P.δ)*z+(2-P.f)*u+P.f*max (u-effRepair P (some 0)) 0 := by
    rw [he,sub_zero,max_eq_left hu.le]
    dsimp [u,z,puFull,pnFull]
    field_simp [ne_of_gt hd,ne_of_gt hden]
    ring
  refine ⟨u/P.δ,z,hpn,?_,?_,?_⟩
  · intro r hr; cases Option.some.inj hr; exact le_rfl
  · apply construct_market P hP _ _ _ _ _ _ hu.le (by norm_num) le_rfl hz0 h12 hz1.le
    · field_simp
    · exact hn
    · intro _; rfl
    · intro h; rw [he] at h; linarith
    · rw [hbal]; ring
  · have heq : profit P (pnFull P) (some 0) 1 z=profit4 P (pnFull P) 0 := by
      simp only [profit,if_pos hi,profit4,theta2Problem4,mul_zero,add_zero]
      dsimp [z]
      ring
    rw [heq,full_gap P hP]
    have hl : pnFull P+P.f*0-(P.c+P.δ+P.cM*P.f+1)/2=0 := by unfold pnFull; ring
    rw [hl]; simp
end RepairResearch
namespace RepairResearch
noncomputable def fullValue (P : Params) : ℝ := (P.c-P.δ+P.cM*P.f-1)^2/(4*(1+3*P.δ))
def PartialFeas (P : Params) (z u : ℝ) : Prop :=
  0≤z ∧ z≤1 ∧ 0≤u ∧ u≤P.cI ∧ P.δ*(2*z-1)≤u ∧ u≤P.δ*((2-P.f)*z-(1-P.f))
lemma global_upper (P : Params) (hP : Standing P) (pn : ℝ) (pr : Option ℝ)
    (pu α θ₁ θ₂ : ℝ) (hpn : 0≤pn) (hr : repairAdmissible pr)
    (h : MarketEq P pn pr pu α θ₁ θ₂) :
    profit P pn pr α θ₂≤fullValue P ∨
    ∃ z u, PartialFeas P z u ∧ profit P pn pr α θ₂≤partialF P z u := by
  have h21 : θ₂≤1 := h.2.2.2.2.2.1
  by_cases ht : θ₂<1
  · by_cases hp : 0<pu
    · by_cases he : effRepair P pr<pu
      · exact Or.inl (full_profit_bound P hP pn pr pu α θ₁ θ₂ h hp ht he)
      · have he' : pu≤effRepair P pr := le_of_not_gt he
        have hb := positive_partial_bounds P hP pn pr pu α θ₁ θ₂ h hp ht he'
        exact Or.inr ⟨θ₂,pu,⟨h.2.2.2.1.trans h.2.2.2.2.1,h21,hp.le,hb.1,hb.2.1,hb.2.2.1⟩,
          partial_profit_bound P hP pn pr pu α θ₁ θ₂ h hp ht he'⟩
    · have hp0 : pu=0 := le_antisymm (le_of_not_gt hp) h.1
      subst pu
      obtain ⟨z,hz0,hz1,hl,hh,hv⟩ := zero_profit_bound P hP pn pr α θ₁ θ₂ h hpn hr ht
      exact Or.inr ⟨z,0,⟨hz0,hz1,le_rfl,hP.cM_nonneg.trans hP.cM_le_cI,hl,hh⟩,hv⟩
  · have hz : θ₂=1 := le_antisymm h21 (le_of_not_gt ht)
    rw [hz]
    left
    have hzero : profit P pn pr α 1=0 := by cases pr <;> simp [profit]
    rw [hzero]
    unfold fullValue
    have hd := hP.δ_pos
    positivity
lemma optimal_of_reduced (P : Params) (hP : Standing P) (pn : ℝ) (pr : Option ℝ)
    (pu α θ₁ θ₂ : ℝ) (hpn : 0≤pn) (hr : repairAdmissible pr)
    (h : MarketEq P pn pr pu α θ₁ θ₂)
    (hfull : fullValue P≤profit P pn pr α θ₂)
    (hpartial : ∀ z u, PartialFeas P z u → partialF P z u≤profit P pn pr α θ₂) :
    OptimalOutcome P pn pr pu α := by
  refine ⟨hpn,hr,θ₁,θ₂,h,?_⟩
  intro pn' pr' pu' α' θ₁' θ₂' hpn' hr' h'
  rcases global_upper P hP pn' pr' pu' α' θ₁' θ₂' hpn' hr' h' with h' | ⟨z,u,hzu,h'⟩
  · exact h'.trans hfull
  · exact h'.trans (hpartial z u hzu)
end RepairResearch
namespace RepairResearch
noncomputable def zs (P : Params) : ℝ := (1-P.δ+P.c-P.cM*(2-P.f))/(2*(1-P.δ))
noncomputable def us (P : Params) : ℝ := (P.δ+P.cM)/2
noncomputable def zn (P : Params) : ℝ := (pnNo P+P.δ*(1-P.f)*(2-P.f))/(1+P.δ*(1-P.f)*(3-P.f))
noncomputable def un (P : Params) : ℝ := puNo P
noncomputable def zf (P : Params) : ℝ := (2*P.δ+pnFull P)/(1+3*P.δ)
noncomputable def uf (P : Params) : ℝ := puFull P
lemma grad_gap (P : Params) (z u Z U : ℝ) :
    partialF P Z U-partialF P z u = (1-P.δ)*(z-Z)^2+(u-U)^2/P.δ-
      (1-P.δ+P.c-P.cM*(2-P.f)-2*(1-P.δ)*Z)*(z-Z)-
      (1+P.cM/P.δ-2*U/P.δ)*(u-U) := by
  unfold partialF;ring
lemma grad_upper (P : Params) (hP : Standing P) (Z U z u : ℝ)
    (h : (1-P.δ+P.c-P.cM*(2-P.f)-2*(1-P.δ)*Z)*(z-Z)+
      (1+P.cM/P.δ-2*U/P.δ)*(u-U)≤0) : partialF P z u≤partialF P Z U := by
  have hg := grad_gap P z u Z U
  have h1 := mul_nonneg (sub_nonneg.mpr hP.δ_lt_one.le) (sq_nonneg (z-Z))
  have h2 := div_nonneg (sq_nonneg (u-U)) hP.δ_pos.le
  linarith
lemma full_point (P : Params) (hP : Standing P) :
    uf P=P.δ*(2*zf P-1) ∧ zf P<1 ∧ partialF P (zf P) (uf P)=fullValue P := by
  have hd : P.δ≠0 := ne_of_gt hP.δ_pos
  have hδ := hP.δ_pos
  have hden : 0<1+3*P.δ := by linarith [hP.δ_pos]
  refine ⟨?_,?_,?_⟩
  · unfold uf zf puFull pnFull
    field_simp [ne_of_gt hden]
    ring_nf <;> field_simp [show 1+P.δ*3≠0 by linarith] <;> ring
  · unfold zf pnFull
    apply (div_lt_one hden).mpr
    linarith [hP.c_lt]
  · unfold partialF fullValue zf uf pnFull puFull
    field_simp [hd,ne_of_gt hden]
    ring_nf <;> field_simp [show 1+P.δ*3≠0 by linarith [hP.δ_pos], show 1+P.δ*6+P.δ^2*9≠0 by positivity] <;> ring
lemma full_region_bound (P : Params) (hP : Standing P) (hc : cBar P≤P.c)
    (z u : ℝ) (h : P.δ*(2*z-1)≤u) : partialF P z u≤fullValue P := by
  have hd : 0<P.δ := hP.δ_pos
  have hden : 0<1+3*P.δ := by positivity
  have hp := full_point P hP
  rw [← hp.2.2]
  apply grad_upper P hP
  have hmult : 1+P.cM/P.δ-2*uf P/P.δ≤0 := by
    unfold cBar at hc
    have hc' := (div_le_iff₀ (by positivity : 0<2*P.δ)).mp hc
    unfold uf puFull
    field_simp [ne_of_gt hd,ne_of_gt hden]
    nlinarith
  have hid : 1-P.δ+P.c-P.cM*(2-P.f)-2*(1-P.δ)*zf P =
      -2*P.δ*(1+P.cM/P.δ-2*uf P/P.δ) := by
    unfold zf uf pnFull puFull
    field_simp [ne_of_gt hd,ne_of_gt hden]
    ring
  rw [hid]
  have hb : 0≤u-uf P-2*P.δ*(z-zf P) := by rw [hp.1];nlinarith [h]
  have hm := mul_nonpos_of_nonpos_of_nonneg hmult hb
  nlinarith
lemma full_region (P : Params) (hP : Standing P) (hc : cBar P≤P.c) :
    OptimalOutcome P (pnFull P) (some 0) (puFull P) 1 := by
  obtain ⟨t,z,hpn,hr,he,hv⟩ := full_construct P hP
  apply optimal_of_reduced P hP _ _ _ _ _ _ hpn hr he
  · exact le_of_eq hv.symm
  · intro z' u' h
    rw [hv]
    exact full_region_bound P hP hc z' u' h.2.2.2.2.1
lemma interior_bound (P : Params) (hP : Standing P) (z u : ℝ) :
    partialF P z u≤partialF P (zs P) (us P) := by
  have hh := partial_gap P hP z u
  change partialF P (zs P) (us P)-partialF P z u=(1-P.δ)*(z-zs P)^2+(u-us P)^2/P.δ at hh
  have h1 := mul_nonneg (sub_nonneg.mpr hP.δ_lt_one.le) (sq_nonneg (z-zs P))
  have h2 := div_nonneg (sq_nonneg (u-us P)) hP.δ_pos.le
  linarith
lemma interior_full_bound (P : Params) (hP : Standing P) :
    fullValue P≤partialF P (zs P) (us P) := by
  rw [← (full_point P hP).2.2]
  exact interior_bound P hP _ _
end RepairResearch
namespace RepairResearch
lemma alpha_identity (P : Params) (hP : Standing P) (z u : ℝ) (hz : z<1) :
    alphaHat P ((1-P.δ)*z+(2-P.f)*u) u =
      ((2-P.f)*z-(1-P.f)-u/P.δ)/(P.f*(1-z)) := by
  have hd : P.δ≠0 := ne_of_gt hP.δ_pos
  have hf : P.f≠0 := ne_of_gt hP.f_pos
  have h1 : 1-P.δ≠0 := ne_of_gt (sub_pos.mpr hP.δ_lt_one)
  have hz1 : 1-z≠0 := ne_of_gt (sub_pos.mpr hz)
  unfold alphaHat
  rw [show (1-P.δ)*z+(2-P.f)*u-(2-P.f)*u+P.δ-1 = -(1-P.δ)*(1-z) by ring]
  field_simp
  ring
lemma interior_region (P : Params) (hP : Standing P) (hi : us P≤P.cI)
    (hl : cLow P<P.c) (hh : P.c<cBar P) :
    OptimalOutcome P (pnNo P) (some (us P)) (us P) (alphaHat P (pnNo P) (us P)) ∧
    0<alphaHat P (pnNo P) (us P) ∧ alphaHat P (pnNo P) (us P)<1 := by
  have hd : 0<P.δ := hP.δ_pos
  have hf : 0<P.f := hP.f_pos
  have h1 : 0<1-P.δ := sub_pos.mpr hP.δ_lt_one
  have hf1 : 0<1-P.f := sub_pos.mpr hP.f_lt_one
  have hf2 : 0<2-P.f := by linarith [hP.f_lt_one]
  have hu0 : 0<us P := by unfold us;linarith [hP.cM_nonneg]
  have huδ : us P<P.δ := by unfold us;linarith [hP.cM_lt_δ]
  have hupper : us P<P.δ*((2-P.f)*zs P-(1-P.f)) := by
    have he : P.δ*((2-P.f)*zs P-(1-P.f))-us P =
        P.δ*(2-P.f)/(2*(1-P.δ))*(P.c-cLow P) := by
      unfold zs us cLow
      field_simp
      ring
    have hp : 0<P.δ*(2-P.f)/(2*(1-P.δ))*(P.c-cLow P) := by positivity
    linarith
  have hlower : P.δ*(2*zs P-1)<us P := by
    have he : us P-P.δ*(2*zs P-1) = P.δ/(1-P.δ)*(cBar P-P.c) := by
      unfold zs us cBar
      field_simp
      ring
    have hp : 0<P.δ/(1-P.δ)*(cBar P-P.c) := by positivity
    linarith
  have hz0 : 0≤zs P := by
    have hp : 0<(2-P.f)*zs P-(1-P.f) := (mul_pos_iff_of_pos_left hd).mp (hu0.trans hupper)
    have hz : 0<(2-P.f)*zs P := by linarith
    exact ((mul_pos_iff_of_pos_left hf2).mp hz).le
  have hz1 : zs P<1 := by nlinarith [hlower,huδ]
  have hn : pnNo P=(1-P.δ)*zs P+(2-P.f)*us P := by
    unfold pnNo zs us
    field_simp
    ring
  have ha := alpha_identity P hP (zs P) (us P) hz1
  rw [← hn] at ha
  have hden : 0<P.f*(1-zs P) := mul_pos hf (sub_pos.mpr hz1)
  have hal : 0<alphaHat P (pnNo P) (us P) := by
    rw [ha]
    apply div_pos _ hden
    have := (div_lt_iff₀ hd).mpr (by nlinarith [hupper] : us P<((2-P.f)*zs P-(1-P.f))*P.δ)
    nlinarith
  have hah : alphaHat P (pnNo P) (us P)<1 := by
    rw [ha]
    apply (div_lt_one hden).mpr
    have := (lt_div_iff₀ hd).mpr (by nlinarith [hlower] : (2*zs P-1)*P.δ<us P)
    nlinarith
  obtain ⟨hpn,hr,he,hv⟩ := partial_construct P hP (zs P) (us P) hz0 hz1 hu0.le hi hlower.le hupper.le
  rw [← hn] at hpn
  rw [← hn,← ha] at he hv
  refine ⟨?_,hal,hah⟩
  apply optimal_of_reduced P hP _ _ _ _ _ _ hpn hr he
  · rw [hv];exact interior_full_bound P hP
  · intro z u _;rw [hv];exact interior_bound P hP z u
end RepairResearch
namespace RepairResearch
lemma no_identities (P : Params) (hP : Standing P) :
    un P=P.δ*((2-P.f)*zn P-(1-P.f)) ∧
    pnNo P=(1-P.δ)*zn P+(2-P.f)*un P ∧
    (1-P.δ+P.c-P.cM*(2-P.f)-2*(1-P.δ)*zn P)=
      -P.δ*(2-P.f)*(1+P.cM/P.δ-2*un P/P.δ) ∧
    (1+P.cM/P.δ-2*un P/P.δ)=(2-P.f)*(cLow P-P.c)/(1+P.δ*(1-P.f)*(3-P.f)) := by
  have hd : P.δ≠0 := ne_of_gt hP.δ_pos
  have hf : 0<2-P.f := by linarith [hP.f_lt_one]
  have hA : 0<1+P.δ*(1-P.f)*(3-P.f) := by
    have hdpos := hP.δ_pos
    have hf1 : 0<1-P.f := sub_pos.mpr hP.f_lt_one
    have hf3 : 0<3-P.f := by linarith
    positivity
  unfold un zn pnNo puNo cLow
  constructor
  · field_simp [ne_of_gt hA];ring
  constructor
  · field_simp [ne_of_gt hA];ring
  constructor
  · field_simp [hd,ne_of_gt hA];ring
  · field_simp [hd,ne_of_gt hf,ne_of_gt hA];ring
lemma no_region_bound (P : Params) (hP : Standing P) (hc : P.c≤cLow P)
    (z u : ℝ) (h : u≤P.δ*((2-P.f)*z-(1-P.f))) :
    partialF P z u≤partialF P (zn P) (un P) := by
  have hh := no_identities P hP
  have hd := hP.δ_pos
  have hf1 : 0<1-P.f := sub_pos.mpr hP.f_lt_one
  have hf2 : 0<2-P.f := by linarith
  have hf3 : 0<3-P.f := by linarith
  have hm : 0≤1+P.cM/P.δ-2*un P/P.δ := by rw [hh.2.2.2];positivity
  apply grad_upper P hP
  rw [hh.2.2.1]
  have hb : u-un P-P.δ*(2-P.f)*(z-zn P)≤0 := by rw [hh.1];nlinarith [h]
  have hp := mul_nonpos_of_nonneg_of_nonpos hm hb
  nlinarith
lemma no_full_bound (P : Params) (hP : Standing P) (hc : P.c≤cLow P) :
    fullValue P≤partialF P (zn P) (un P) := by
  have hh := full_point P hP
  rw [← hh.2.2]
  apply no_region_bound P hP hc
  rw [hh.1]
  have hp := mul_nonneg hP.δ_pos.le (mul_nonneg hP.f_pos.le (sub_nonneg.mpr hh.2.1.le))
  nlinarith
lemma no_construct (P : Params) (hP : Standing P) (hc : P.c≤cLow P) (hi : un P≤P.cI) :
    ∃ t z,0≤pnNo P ∧ repairAdmissible (none : Option ℝ) ∧
      MarketEq P (pnNo P) none (un P) 0 t z ∧ profit P (pnNo P) none 0 z=partialF P (zn P) (un P) := by
  have hd : 0<P.δ := hP.δ_pos
  have hf : 0<P.f := hP.f_pos
  have hf1 : 0<1-P.f := sub_pos.mpr hP.f_lt_one
  have hf2 : 0<2-P.f := by linarith
  have hf3 : 0<3-P.f := by linarith
  have h1 : 0<1-P.δ := sub_pos.mpr hP.δ_lt_one
  have hA : 0<1+P.δ*(1-P.f)*(3-P.f) := by positivity
  have hh := no_identities P hP
  have hpn : 0<pnNo P := by unfold pnNo;have := hP.c_nonneg;positivity
  have hz0 : 0<zn P := by unfold zn;positivity
  have hcap : P.c<1+P.δ*(1-P.f) := by
    have he : 1+P.δ*(1-P.f)-cLow P=
        (1+P.δ*(1-P.f)*(3-P.f))*(P.δ-P.cM)/(P.δ*(2-P.f)) := by
      unfold cLow;field_simp;ring
    have hpos : 0<(1+P.δ*(1-P.f)*(3-P.f))*(P.δ-P.cM)/(P.δ*(2-P.f)) := by
      have := hP.cM_lt_δ;positivity
    linarith
  have hz1 : zn P<1 := by
    unfold zn pnNo
    apply (div_lt_one hA).mpr
    nlinarith [hcap]
  have hu0 : 0≤un P := by
    have he : 2*(1+P.δ*(1-P.f)*(3-P.f))*un P=
        P.δ*((2-P.f)*P.c+P.f+P.δ*(1-P.f)*(4-P.f)) := by
      unfold un puNo;field_simp;ring
    have hpos : 0≤P.δ*((2-P.f)*P.c+P.f+P.δ*(1-P.f)*(4-P.f)) := by
      have hcpos := hP.c_nonneg
      have hf4 : 0<4-P.f := by linarith
      positivity
    nlinarith
  have h10 : 0≤un P/P.δ := div_nonneg hu0 hd.le
  have hbal : zn P-un P/P.δ=(1-zn P)*(1-P.f) := by rw [hh.1];field_simp;ring
  have h12 : un P/P.δ≤zn P := by
    have hp := mul_nonneg (sub_nonneg.mpr hz1.le) hf1.le
    linarith
  have he : effRepair P none=P.cI := rfl
  refine ⟨un P/P.δ,zn P,hpn.le,by simp [repairAdmissible],?_,?_⟩
  · apply construct_market P hP _ _ _ _ _ _ hu0 (by norm_num) (by norm_num) h10 h12 hz1.le
    · field_simp
    · rw [he,max_eq_right (sub_nonpos.mpr hi),mul_zero,add_zero];exact hh.2.1
    · intro h;rw [he] at h;linarith
    · intro _;rfl
    · simpa using hbal
  · have hq := partial_quadratic P hP (zn P) (un P)
    change _=partialF P (zn P) (un P) at hq
    have hs : (2-P.f)*zn P-(1-P.f)-un P/P.δ=0 := by rw [hh.1];field_simp;ring
    rw [hs,mul_zero,add_zero,← hh.2.1] at hq
    simpa [profit] using hq
lemma no_region (P : Params) (hP : Standing P) (hc : P.c≤cLow P) (hi : un P≤P.cI) :
    OptimalOutcome P (pnNo P) none (un P) 0 := by
  obtain ⟨t,z,hpn,hr,he,hv⟩ := no_construct P hP hc hi
  apply optimal_of_reduced P hP _ _ _ _ _ _ hpn hr he
  · rw [hv];exact no_full_bound P hP hc
  · intro z' u' h;rw [hv];exact no_region_bound P hP hc z' u' h.2.2.2.2.2
lemma no_high_region (P : Params) (hP : Standing P) (hc : P.c≤cLow P) (hi : us P≤P.cI) :
    OptimalOutcome P (pnNo P) none (puNo P) 0 := by
  apply no_region P hP hc
  apply le_trans _ hi
  have hd := hP.δ_pos
  have hf1 : 0<1-P.f := sub_pos.mpr hP.f_lt_one
  have hf2 : 0<2-P.f := by linarith
  have hf3 : 0<3-P.f := by linarith
  have he : us P-un P=P.δ*(2-P.f)*(cLow P-P.c)/(2*(1+P.δ*(1-P.f)*(3-P.f))) := by
    unfold us un puNo cLow;field_simp;ring
  have hp : 0≤P.δ*(2-P.f)*(cLow P-P.c)/(2*(1+P.δ*(1-P.f)*(3-P.f))) := by positivity
  linarith
end RepairResearch

namespace RepairResearch
lemma interior_weak_region (P : Params) (hP : Standing P) (hi : us P≤P.cI)
    (hl : cLow P≤P.c) (hh : P.c<cBar P) :
    OptimalOutcome P (pnNo P) (some (us P)) (us P) (alphaHat P (pnNo P) (us P)) ∧
    0≤alphaHat P (pnNo P) (us P) ∧ alphaHat P (pnNo P) (us P)<1 := by
  have hd : 0<P.δ := hP.δ_pos
  have hf : 0<P.f := hP.f_pos
  have h1 : 0<1-P.δ := sub_pos.mpr hP.δ_lt_one
  have hf1 : 0<1-P.f := sub_pos.mpr hP.f_lt_one
  have hf2 : 0<2-P.f := by linarith [hP.f_lt_one]
  have hu0 : 0<us P := by unfold us;linarith [hP.cM_nonneg]
  have huδ : us P<P.δ := by unfold us;linarith [hP.cM_lt_δ]
  have hupper : us P≤P.δ*((2-P.f)*zs P-(1-P.f)) := by
    have he : P.δ*((2-P.f)*zs P-(1-P.f))-us P =
        P.δ*(2-P.f)/(2*(1-P.δ))*(P.c-cLow P) := by
      unfold zs us cLow
      field_simp
      ring
    have hp : 0≤P.δ*(2-P.f)/(2*(1-P.δ))*(P.c-cLow P) := by positivity
    linarith
  have hlower : P.δ*(2*zs P-1)<us P := by
    have he : us P-P.δ*(2*zs P-1) = P.δ/(1-P.δ)*(cBar P-P.c) := by
      unfold zs us cBar
      field_simp
      ring
    have hp : 0<P.δ/(1-P.δ)*(cBar P-P.c) := by positivity
    linarith
  have hz0 : 0≤zs P := by
    have hp : 0<(2-P.f)*zs P-(1-P.f) := (mul_pos_iff_of_pos_left hd).mp (hu0.trans_le hupper)
    have hz : 0<(2-P.f)*zs P := by linarith
    exact ((mul_pos_iff_of_pos_left hf2).mp hz).le
  have hz1 : zs P<1 := by nlinarith [hlower,huδ]
  have hn : pnNo P=(1-P.δ)*zs P+(2-P.f)*us P := by
    unfold pnNo zs us
    field_simp
    ring
  have ha := alpha_identity P hP (zs P) (us P) hz1
  rw [← hn] at ha
  have hden : 0<P.f*(1-zs P) := mul_pos hf (sub_pos.mpr hz1)
  have hal : 0≤alphaHat P (pnNo P) (us P) := by
    rw [ha]
    apply div_nonneg _ hden.le
    have := (div_le_iff₀ hd).mpr (by nlinarith [hupper] : us P≤((2-P.f)*zs P-(1-P.f))*P.δ)
    nlinarith
  have hah : alphaHat P (pnNo P) (us P)<1 := by
    rw [ha]
    apply (div_lt_one hden).mpr
    have := (lt_div_iff₀ hd).mpr (by nlinarith [hlower] : (2*zs P-1)*P.δ<us P)
    nlinarith
  obtain ⟨hpn,hr,he,hv⟩ := partial_construct P hP (zs P) (us P) hz0 hz1 hu0.le hi hlower.le hupper
  rw [← hn] at hpn
  rw [← hn,← ha] at he hv
  refine ⟨?_,hal,hah⟩
  apply optimal_of_reduced P hP _ _ _ _ _ _ hpn hr he
  · rw [hv];exact interior_full_bound P hP
  · intro z u _;rw [hv];exact interior_bound P hP z u
end RepairResearch


theorem solution (P : Params) (hP : Standing P)
    (hI : P.δ ≤ P.cI) :
    (P.c < cLow P →
      OptimalOutcome P (pnNo P) none (puNo P) 0) ∧
    (cLow P ≤ P.c → P.c < cBar P →
      OptimalOutcome P (pnNo P) (some ((P.δ + P.cM) / 2))
        ((P.δ + P.cM) / 2)
        (alphaHat P (pnNo P) ((P.δ + P.cM) / 2))) ∧
    (cLow P < P.c → P.c < cBar P →
      0 < alphaHat P (pnNo P) ((P.δ + P.cM) / 2) ∧
      alphaHat P (pnNo P) ((P.δ + P.cM) / 2) < 1) ∧
    (cBar P ≤ P.c →
      OptimalOutcome P (pnFull P) (some 0) (puFull P) 1) := by
  have hi : RepairResearch.us P≤P.cI := by
    unfold RepairResearch.us
    linarith [hP.cM_lt_δ]
  refine ⟨?_,?_,?_,?_⟩
  · intro hc;exact RepairResearch.no_high_region P hP hc.le hi
  · intro hl hh;exact (RepairResearch.interior_weak_region P hP hi hl hh).1
  · intro hl hh;exact (RepairResearch.interior_region P hP hi hl hh).2
  · intro hc;exact RepairResearch.full_region P hP hc


